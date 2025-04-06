#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>
#include <map>
#include <set>
#include <algorithm>
#include <filesystem>
#include <cctype>
#include <stdexcept>
#include <iterator>
#include <exception>
#include <iomanip> // For formatting tables
#include <limits>  // For numeric_limits

using namespace std;
namespace fs = std::filesystem;

// Type alias for CLR(1) item: { rule_with_dot, lookahead_char }
using Clr1Item = pair<string, char>;

// --- Helper Functions ---

// Replaces "->" with "->."
string add_dot_after_arrow(const string &production) {
    size_t arrow_pos = production.find("->");
    if (arrow_pos == string::npos) {
        // Should not happen with valid grammar, but handle defensively
        return "." + production;
    }
    string modified_prod = production;
    modified_prod.insert(arrow_pos + 2, ".");
    return modified_prod;
}

// Sorts items within a state for canonical representation
vector<Clr1Item> get_sorted_state(const vector<Clr1Item>& state) {
    vector<Clr1Item> sorted_state = state;
    // Sort primarily by rule string, secondarily by lookahead char
    sort(sorted_state.begin(), sorted_state.end());
    return sorted_state;
}

// Function: get_terminals
set<char> get_terminals(const vector<string>& gram) {
    set<char> terms;
    for (const string& p : gram) {
        size_t arrowPos = p.find("->");
        if (arrowPos == string::npos) continue;
        string right = p.substr(arrowPos + 2);
        for (char t : right) {
            // islower or !isupper covers terminals, handles symbols like '+' '*' '(' ')' etc.
            // Ensure it's not the special epsilon character if used (e.g., '@')
            if (!isupper(t) && t != '.' && t != '\0' /* && t != EPSILON */) {
                terms.insert(t);
            }
        }
    }
    terms.insert('$'); // Add end-of-input marker
    return terms;
}

// Function: get_non_terminals
set<char> get_non_terminals(const vector<string>& gram) {
    set<char> non_terms;
    for (const string& p : gram) {
        size_t arrowPos = p.find("->");
        if (arrowPos != string::npos && arrowPos > 0 && isupper(p[0])) {
            non_terms.insert(p[0]);
        }
        // Add RHS non-terminals as well, as they might not appear on LHS
        if (arrowPos != string::npos) {
             string right = p.substr(arrowPos + 2);
             for (char t : right) {
                 if (isupper(t)) {
                     non_terms.insert(t);
                 }
             }
        }
    }
     // Ensure start symbol of the *original* grammar is included
     if (!gram.empty()) {
         size_t arrowPosFirst = gram[0].find("->");
         if(arrowPosFirst != string::npos && arrowPosFirst > 0 && isupper(gram[0][0])) {
              non_terms.insert(gram[0][0]);
         } else if (!gram.empty() && isupper(gram[0][0])) {
             // Maybe handle cases like "S" on its own line if grammar format allows
             // For "A->b" format, the above is sufficient.
         }
     }
    return non_terms;
}


// --- FIRST Set Computation ---
const char EPSILON = '@'; // Define a character to represent epsilon

// Computes the FIRST set for a sequence of grammar symbols (terminals/non-terminals)
set<char> first_of_sequence(
    const string& sequence,
    const map<char, set<char>>& first_sets,
    const set<char>& non_terminals)
{
    set<char> result;
    bool all_derive_epsilon = true;

    for (char symbol : sequence) {
        set<char> symbol_first;
        if (non_terminals.count(symbol)) {
            if (first_sets.count(symbol)) {
                symbol_first = first_sets.at(symbol);
            } else {
                 // Should not happen if first_sets are computed correctly
                 cerr << "Warning: FIRST set not found for non-terminal '" << symbol << "'" << endl;
                 // Treat as if it can only derive epsilon to avoid infinite loops maybe? Or throw?
                 // Let's assume it's computed and proceed. If it crashes later, this is why.
            }
        } else if (symbol == EPSILON) {
            symbol_first.insert(EPSILON);
        }
         else { // Terminal
            symbol_first.insert(symbol);
        }

        // Add all non-epsilon symbols from FIRST(symbol) to the result
        for (char f : symbol_first) {
            if (f != EPSILON) {
                result.insert(f);
            }
        }

        // If FIRST(symbol) does not contain epsilon, we stop
        if (symbol_first.find(EPSILON) == symbol_first.end()) {
            all_derive_epsilon = false;
            break;
        }
    }

    // If all symbols in the sequence could derive epsilon, add epsilon to the result
    if (all_derive_epsilon) {
        result.insert(EPSILON);
    }

    return result;
}


// Computes the FIRST sets for all non-terminals in the grammar
map<char, set<char>> compute_first_sets(const vector<string>& grammar_productions, const set<char>& non_terminals, const set<char>& terminals) {
    map<char, set<char>> first_sets;

    // Initialize FIRST(T) = {T} for all terminals T
    for (char t : terminals) {
        first_sets[t].insert(t);
    }
    first_sets[EPSILON].insert(EPSILON); // FIRST of epsilon is {epsilon}
    first_sets['$'].insert('$');         // Treat $ like a terminal

    // Initialize FIRST(N) = {} for all non-terminals N
    for (char nt : non_terminals) {
        first_sets[nt] = set<char>();
    }

    bool changed = true;
    while (changed) {
        changed = false;
        for (const string& prod : grammar_productions) {
            size_t arrow_pos = prod.find("->");
            if (arrow_pos == string::npos || arrow_pos == 0) continue; // Skip invalid lines

            char lhs = prod[0];
            if (!non_terminals.count(lhs)) continue; // LHS must be a non-terminal

            string rhs = prod.substr(arrow_pos + 2);
            if (rhs.empty()) rhs = string(1, EPSILON); // Represent empty RHS as epsilon


            set<char> rhs_first = first_of_sequence(rhs, first_sets, non_terminals);

            // Check if adding rhs_first to FIRST(lhs) changes anything
            size_t old_size = first_sets[lhs].size();
            first_sets[lhs].insert(rhs_first.begin(), rhs_first.end());
            if (first_sets[lhs].size() > old_size) {
                changed = true;
            }
        }
    }

    return first_sets;
}


// --- Core CLR(1) Functions ---

// Function: closure
// Computes the closure of a set of CLR(1) items.
vector<Clr1Item> closure(const vector<Clr1Item>& initial_items,
                         const vector<string>& grammar_productions,
                         const map<char, set<char>>& first_sets,
                         const set<char>& non_terminals)
{
    vector<Clr1Item> current_closure = initial_items;
    vector<Clr1Item> worklist = initial_items; // Items to process

    // Use a set for quick existence checks (pair comparison works)
    set<Clr1Item> closure_set(initial_items.begin(), initial_items.end());

    int processed_count = 0; // Use index instead of pop_back for stable iteration if needed
    while(processed_count < worklist.size()){
        Clr1Item item = worklist[processed_count++]; // Get item without removing from worklist yet
        string rule = item.first;
        char lookahead = item.second;

        size_t dot_pos = rule.find('.');
        // Check if dot exists and is not at the very end
        if (dot_pos != string::npos && dot_pos + 1 < rule.size()) {
            char symbol_after_dot = rule[dot_pos + 1];

            // If it's a non-terminal, add its productions
            if (non_terminals.count(symbol_after_dot)) {
                // Find FIRST set of (sequence after B + original lookahead)
                // Example: item is [A -> alpha . B beta, a]
                // We need FIRST(beta + a)
                string sequence_after_B;
                if (dot_pos + 2 < rule.size()) {
                    sequence_after_B = rule.substr(dot_pos + 2);
                }
                sequence_after_B += lookahead; // Append original lookahead

                set<char> lookaheads_for_new_items = first_of_sequence(sequence_after_B, first_sets, non_terminals);

                // Add productions for B
                for (const string& prod : grammar_productions) {
                    // Check if production starts with the symbol after the dot (B)
                    if (!prod.empty() && prod[0] == symbol_after_dot) {
                        string new_item_base = prod;
                        string new_item_dotted = add_dot_after_arrow(new_item_base);

                        // For each terminal 'b' in FIRST(beta + a)
                        for (char b : lookaheads_for_new_items) {
                            if (b == EPSILON) continue; // Epsilon is not a lookahead terminal

                             Clr1Item new_item = {new_item_dotted, b};

                             // Add to closure and worklist only if it's new
                             if (closure_set.find(new_item) == closure_set.end()) {
                                 closure_set.insert(new_item);
                                 current_closure.push_back(new_item);
                                 worklist.push_back(new_item); // Add to end of worklist
                             }
                        }
                    }
                }
            }
        }
        // No 'else' needed here - if dot is at end or symbol after dot is terminal, no expansion occurs
    }
    // Sort the final closure for canonical representation before returning
    return get_sorted_state(current_closure);
}

// Function: goto_set
// Computes the GOTO set for a given state (set of items) and a grammar symbol.
vector<Clr1Item> goto_set(const vector<Clr1Item>& state_items,
                          char symbol,
                          const vector<string>& grammar_productions,
                          const map<char, set<char>>& first_sets,
                          const set<char>& non_terminals)
{
    vector<Clr1Item> kernel_items;
    for (const Clr1Item& item : state_items) {
        string rule = item.first;
        char lookahead = item.second;
        size_t dot_pos = rule.find('.');

        if (dot_pos != string::npos && dot_pos + 1 < rule.size()) {
            if (rule[dot_pos + 1] == symbol) {
                // Move the dot one position to the right
                string next_rule = rule;
                swap(next_rule[dot_pos], next_rule[dot_pos + 1]);
                // Lookahead remains the same in GOTO transition
                kernel_items.push_back({next_rule, lookahead});
            }
        }
    }
    // Return the closure of the kernel items
    // Need to pass dependencies for closure calculation
    return closure(kernel_items, grammar_productions, first_sets, non_terminals);
}


// Function: generate_states_and_dfa
// Generates all CLR(1) states and the DFA transitions.
void generate_states_and_dfa(
    const vector<string>& grammar_productions,      // Original grammar rules (needed for closure)
    const string& augmented_start_rule,            // E.g., "X->S" (rule string only)
    const map<char, set<char>>& first_sets,         // Precomputed FIRST sets
    const set<char>& non_terminals,                 // Set of non-terminals
    vector<vector<Clr1Item>>& canonical_collection, // Output: List of states (each state is a vector<Clr1Item>)
    map<int, map<char, int>>& dfa_goto             // Output: DFA transitions map<from_state, map<symbol, to_state>>
) {
    canonical_collection.clear();
    dfa_goto.clear();

    // Map canonical (sorted) state (vector<Clr1Item>) to its ID
    // Need a custom comparator for map keys if vector<pair> is used directly,
    // or convert state to a string/tuple, or use std::map's default comparison
    // which works element-wise for vectors of pairs.
    map<vector<Clr1Item>, int> state_to_id;
    vector<vector<Clr1Item>> states_to_process; // Worklist of states

    // 1. Initial State (Closure of augmented start rule item [X -> .S, $])
    string start_item_rule = add_dot_after_arrow(augmented_start_rule);
    Clr1Item initial_clr_item = {start_item_rule, '$'}; // Start lookahead is $

    vector<Clr1Item> initial_state_items = closure({initial_clr_item}, grammar_productions, first_sets, non_terminals);
    // initial_state_items is already sorted by closure function

    canonical_collection.push_back(initial_state_items);
    state_to_id[initial_state_items] = 0;
    states_to_process.push_back(initial_state_items);

    int current_id = 0;

    // 2. Process states from the worklist
    while (current_id < states_to_process.size()) {
        vector<Clr1Item> current_state_items = states_to_process[current_id];
        int from_state_id = state_to_id[current_state_items]; // Should be == current_id

        // Find all possible symbols following a dot in the current state
        set<char> possible_symbols;
        for (const Clr1Item& item : current_state_items) {
            const string& rule = item.first;
            size_t dot_pos = rule.find('.');
            if (dot_pos != string::npos && dot_pos + 1 < rule.size()) {
                possible_symbols.insert(rule[dot_pos + 1]);
            }
        }

        // Calculate GOTO for each symbol
        for (char symbol : possible_symbols) {
             if (symbol == EPSILON) continue; // Cannot transition on epsilon

            vector<Clr1Item> next_state_items = goto_set(current_state_items, symbol, grammar_productions, first_sets, non_terminals);
            // next_state_items is already sorted by closure function (which calls get_sorted_state)

            if (!next_state_items.empty()) {
                // Check if this state (sorted vector<Clr1Item>) already exists
                if (state_to_id.find(next_state_items) == state_to_id.end()) {
                    // New state found
                    int new_state_id = canonical_collection.size();
                    state_to_id[next_state_items] = new_state_id;
                    canonical_collection.push_back(next_state_items);
                    states_to_process.push_back(next_state_items); // Add to worklist
                    dfa_goto[from_state_id][symbol] = new_state_id;
                } else {
                    // Existing state
                    int existing_state_id = state_to_id[next_state_items];
                    dfa_goto[from_state_id][symbol] = existing_state_id;
                }
            }
        }
        current_id++;
    }
}

// Function: build_parsing_table
// Builds the CLR(1) Action and Goto tables. Throws if not CLR(1).
void build_parsing_table(
    const vector<vector<Clr1Item>>& canonical_collection, // All states
    const map<int, map<char, int>>& dfa_goto,             // DFA transitions
    const vector<string>& original_grammar,               // Original rules (for reduce)
    const string& augmented_production_no_dot,            // E.g., "X->S"
    const set<char>& terminals,                           // Set of terminal symbols (inc '$')
    const set<char>& non_terminals,                       // Set of non-terminal symbols
    map<int, map<char, string>>& action_table,            // Output: Action table
    map<int, map<char, int>>& goto_table                  // Output: Goto table
) {
    action_table.clear();
    goto_table.clear(); // Initialize GOTO table separately

    // Populate GOTO table from DFA transitions on non-terminals
    for(const auto& [from_state, transitions] : dfa_goto) {
        for (const auto& [symbol, to_state] : transitions) {
            if (non_terminals.count(symbol)) {
                goto_table[from_state][symbol] = to_state;
            }
        }
    }


    // Map original production string -> number (1-based)
    map<string, int> prod_num;
    for (size_t i = 0; i < original_grammar.size(); ++i) {
        prod_num[original_grammar[i]] = i + 1;
    }

    // Populate ACTION table
    for (int i = 0; i < canonical_collection.size(); ++i) {
        const vector<Clr1Item>& state_items = canonical_collection[i];

        for (const Clr1Item& item : state_items) {
            string rule = item.first;
            char lookahead = item.second; // The crucial lookahead 'a'
            size_t dot_pos = rule.find('.');
            if (dot_pos == string::npos) continue; // Should not happen

            // Case 1: Shift Action ([A -> α . t β, a], where t is a terminal)
            if (dot_pos + 1 < rule.size()) {
                char symbol_after_dot = rule[dot_pos + 1];
                if (terminals.count(symbol_after_dot)) {
                    // Find the target state from DFA GOTO on terminal 'symbol_after_dot'
                    if (dfa_goto.count(i) && dfa_goto.at(i).count(symbol_after_dot)) {
                        int target_state = dfa_goto.at(i).at(symbol_after_dot);
                        string shift_action = "S" + to_string(target_state);

                        // Check for conflicts for ACTION[i, symbol_after_dot]
                        if (action_table.count(i) && action_table[i].count(symbol_after_dot)) {
                            const string& existing_action = action_table[i][symbol_after_dot];
                            if (existing_action != shift_action) {
                                // If existing is Reduce -> Shift/Reduce conflict
                                // If existing is Shift to different state -> Internal error/non-determinism
                                throw runtime_error("Grammar is not CLR(1): Conflict (likely Shift/Reduce) in state " + to_string(i) + " on terminal '" + symbol_after_dot + "'. Existing: " + existing_action + ", New: " + shift_action);
                            }
                             // else, action is the same, no conflict
                        } else {
                            // No existing action, safe to add
                            action_table[i][symbol_after_dot] = shift_action;
                        }
                    } else {
                        // This implies an error in DFA construction if a terminal follows a dot
                        // but no transition exists for it.
                         cerr << "Warning: No DFA transition found for terminal '" << symbol_after_dot << "' from state " << i << ", although item " << rule << " suggests one." << endl;
                    }
                }
                // Transitions on non-terminals are handled by the GOTO table
            }
            // Case 2: Reduce or Accept Action ([A -> α ., a])
            else { // Dot is at the end
                string production_rule = rule.substr(0, dot_pos); // Get rule without dot, e.g., "A->alpha"

                // Special case: Accept state [X -> S ., $]
                if (production_rule == augmented_production_no_dot) {
                     if (lookahead == '$') { // Must have $ as lookahead for accept
                        string accept_action = "Accept";
                        // Check for conflict for ACTION[i, '$']
                        if (action_table.count(i) && action_table[i].count('$')) {
                             const string& existing_action = action_table[i]['$'];
                             if (existing_action != accept_action) {
                                 throw runtime_error("Grammar is not CLR(1): Conflict (Accept vs " + existing_action + ") in state " + to_string(i) + " on '$'.");
                             }
                        } else {
                             action_table[i]['$'] = accept_action;
                        }
                    }
                     // If lookahead is not '$' for the augmented rule end, ignore (shouldn't happen for valid start)
                }
                // Normal Reduce Action [A -> alpha ., a], where A != X
                else {
                    // Find the original production number
                    if (prod_num.count(production_rule)) {
                        int rule_number = prod_num[production_rule];
                        string reduce_action = "r" + to_string(rule_number);

                        // Add reduce action ONLY for the specific lookahead terminal 'lookahead'
                        // Check for conflict for ACTION[i, lookahead]
                         if (action_table.count(i) && action_table[i].count(lookahead)) {
                             const string& existing_action = action_table[i][lookahead];
                             if (existing_action != reduce_action) {
                                 // Could be Shift/Reduce or Reduce/Reduce conflict
                                 throw runtime_error(std::string("Grammar is not CLR(1): Conflict (") +
                                    (existing_action[0] == 'S' ? "Shift/Reduce" : "Reduce/Reduce") +
                                    ") in state " + std::to_string(i) + " on lookahead '" + lookahead +
                                    "'. Existing: " + existing_action + ", New: " + reduce_action +
                                    " (from rule " + production_rule + ")");
                             }
                             // else, action is the same reduce, no conflict
                         } else {
                             // No existing action for this lookahead, safe to add
                             action_table[i][lookahead] = reduce_action;
                         }
                    } else {
                        // This indicates an issue with production mapping (internal error)
                        cerr << "Warning: Could not find production number for reducing rule: " << production_rule << endl;
                    }
                }
            }
        } // End loop over items in state
    } // End loop over states
}


// --- Parsing ---

// Function: parse_input
// Parses the input string using the CLR(1) tables. (Identical structure to LR(0) parse_input)
bool parse_input(
    const string& input_string_with_dollar,
    const map<int, map<char, string>>& action_table,
    const map<int, map<char, int>>& goto_table,
    const vector<string>& original_grammar, // Needed to find RHS length for reduce
    vector<vector<string>>& parse_steps // Output: steps for table display
) {
    parse_steps.clear();
    vector<int> stack;
    stack.push_back(0); // Initial state

    int input_ptr = 0;

    while (true) {
        if (stack.empty()) { // Should not happen in normal operation unless error occurred
             vector<string> step = {"Error: Stack empty", to_string(input_ptr), "?", "[]"};
             parse_steps.push_back(step);
             return false;
        }
        int current_state = stack.back();
        char lookahead = input_string_with_dollar[input_ptr];

        string action;
        bool action_found = false;
         if (action_table.count(current_state)) {
            const auto& state_actions = action_table.at(current_state);
            if (state_actions.count(lookahead)) {
                action = state_actions.at(lookahead);
                action_found = true;
            }
         }

        if (!action_found) {
            // Error: No action defined
            vector<string> step = {"Error: No action", to_string(input_ptr), string(1, lookahead), ""};
            ostringstream stack_oss;
            stack_oss << "[";
             for(size_t j=0; j<stack.size(); ++j) stack_oss << stack[j] << (j == stack.size()-1 ? "" : ", ");
            stack_oss << "]";
            step[3] = stack_oss.str();
            parse_steps.push_back(step);
            cerr << "Parse Error: No action defined for state " << current_state << " and lookahead '" << lookahead << "' at input position " << input_ptr << endl;
            return false; // Parsing failed
        }

        // Record current step BEFORE modifying stack/input_ptr
        vector<string> step = {action, to_string(input_ptr), string(1, lookahead), ""};
        ostringstream stack_oss;
        stack_oss << "[";
        for(size_t j=0; j<stack.size(); ++j) stack_oss << stack[j] << (j == stack.size()-1 ? "" : ", ");
        stack_oss << "]";
        step[3] = stack_oss.str();
        parse_steps.push_back(step);


        if (action == "Accept") {
            return true; // Parsing successful
        } else if (action[0] == 'S') { // Shift
            int target_state = stoi(action.substr(1));
            // stack.push_back(lookahead); // Standard LR pushes symbol THEN state conceptually - we just push state
            stack.push_back(target_state); // Push state
            input_ptr++;
        } else if (action[0] == 'r') { // Reduce
            int rule_number = stoi(action.substr(1));
            // Find the production rule A -> alpha using rule_number (1-based index)
            if (rule_number < 1 || rule_number > original_grammar.size()) {
                 // Record error step before throwing
                 vector<string> err_step = {"Error: Invalid rule number " + to_string(rule_number), to_string(input_ptr), string(1, lookahead), stack_oss.str()};
                 parse_steps.push_back(err_step);
                 throw runtime_error("Internal Error: Invalid rule number " + to_string(rule_number) + " during reduce.");
            }
            string production_rule = original_grammar[rule_number - 1]; // 0-based index

            size_t arrow_pos = production_rule.find("->");
            if (arrow_pos == string::npos) {
                 vector<string> err_step = {"Error: Invalid production format '" + production_rule + "'", to_string(input_ptr), string(1, lookahead), stack_oss.str()};
                 parse_steps.push_back(err_step);
                 throw runtime_error("Internal Error: Invalid production format '" + production_rule + "'");
            }
            string rhs = production_rule.substr(arrow_pos + 2);
             if (rhs == string(1, EPSILON)) rhs = ""; // Handle explicit epsilon representation
            char lhs_non_terminal = production_rule[0];

            // Pop |alpha| states from the stack
            int pop_count = rhs.length();
             if (stack.size() < (size_t)(pop_count + 1)) { // Need at least pop_count states + 1 below them
                  vector<string> err_step = {"Error: Stack underflow during reduce", to_string(input_ptr), string(1, lookahead), stack_oss.str()};
                 parse_steps.push_back(err_step);
                 throw runtime_error("Internal Error: Stack underflow during reduce for rule " + production_rule);
             }
            for (int k = 0; k < pop_count; ++k) {
                stack.pop_back();
            }

            // Find the state exposed after popping
             if (stack.empty()) { // Should be caught by size check above, but defensive
                 vector<string> err_step = {"Error: Stack empty after pop", to_string(input_ptr), string(1, lookahead), "[]"};
                 parse_steps.push_back(err_step);
                 throw runtime_error("Internal Error: Stack became empty unexpectedly after popping for reduce.");
             }
            int exposed_state = stack.back();

            // Look up GOTO state: GOTO[exposed_state, lhs_non_terminal]
            bool goto_found = false;
            int goto_state = -1;
            if (goto_table.count(exposed_state)) {
                const auto& state_gotos = goto_table.at(exposed_state);
                if (state_gotos.count(lhs_non_terminal)) {
                    goto_state = state_gotos.at(lhs_non_terminal);
                    goto_found = true;
                }
            }

            if (!goto_found) {
                // If GOTO is undefined, it's an error in the table construction or grammar
                vector<string> err_step = {"Error: Undefined GOTO(state " + to_string(exposed_state) + ", non-terminal '" + string(1, lhs_non_terminal) + "')", to_string(input_ptr), string(1, lookahead), ""};
                 ostringstream err_stack_oss; // Rebuild stack string for error step
                 err_stack_oss << "[";
                 for(size_t j=0; j<stack.size(); ++j) err_stack_oss << stack[j] << (j == stack.size()-1 ? "" : ", ");
                 err_stack_oss << "]";
                 err_step[3] = err_stack_oss.str();
                parse_steps.push_back(err_step);
                 cerr << "Parse Error: Undefined GOTO for state " << exposed_state << " and non-terminal '" << lhs_non_terminal << "'" << endl;
                return false;
            }

            // Push the GOTO state
            // stack.push_back(lhs_non_terminal); // Symbol (conceptual) - not needed
            stack.push_back(goto_state); // State

        } else {
            // Should not happen if action was found but isn't S, r, or Accept
             vector<string> err_step = {"Error: Unknown action '" + action + "'", to_string(input_ptr), string(1, lookahead), stack_oss.str()};
             parse_steps.push_back(err_step);
             throw runtime_error("Internal Error: Unknown action type '" + action + "'");
        }
    } // end while
}


// --- Utility Functions ---

// Function: compress_name (Simple example)
string compress_name(const string &name) {
    string comp_name;
    for (char c : name) {
        if (isalnum(c)) {
            comp_name += c;
        } else if (comp_name.length() > 0 && comp_name.back() != '_') {
             // Replace sequences of non-alnum with single underscore
             comp_name += '_';
        }
    }
    // Remove trailing underscore
    if (!comp_name.empty() && comp_name.back() == '_') {
        comp_name.pop_back();
    }
     if (comp_name.length() > 50) { // Limit length for filename safety
         comp_name = comp_name.substr(0, 50);
     }
    return comp_name.empty() ? "default" : comp_name;
}

// Function: save_file
void save_file(const string &content, int grammar_num, const string &name_suffix) {
    try {
        string directory = "parsable_strings/" + to_string(grammar_num) + "/";
        fs::create_directories(directory); // Create if it doesn't exist

        string filename = directory + name_suffix + ".txt";
        ofstream f(filename);
        if (!f) {
            cerr << "Error: Could not open file for writing: " << filename << endl;
            return;
        }
        f << content;
        f.close();
        cout << "Output saved to " << filename << "\n"; // More informative message
    } catch (const fs::filesystem_error& e) {
        cerr << "Filesystem error when saving file: " << e.what() << endl;
    } catch (const exception& e) {
         cerr << "Error saving file: " << e.what() << endl;
    }
}

// Function: format_table_to_string (Improved ASCII table formatting)
string format_table_to_string(const vector<vector<string>>& data, const vector<string>& header) {
     if (header.empty() && data.empty()) return "Table is empty.\n";
     size_t num_cols = header.empty() ? (data.empty() ? 0 : data[0].size()) : header.size();
     if (num_cols == 0) return "Table has no columns.\n";

     vector<size_t> col_widths(num_cols, 0);

     // Calculate widths based on header
     for (size_t j = 0; j < num_cols; ++j) {
         if (j < header.size()) {
            col_widths[j] = max(col_widths[j], header[j].length());
         } else {
             col_widths[j] = 4; // Default width for missing header
         }
     }
     // Calculate widths based on data
     for (const auto& row : data) {
         for (size_t j = 0; j < num_cols; ++j) {
            if (j < row.size()) {
                col_widths[j] = max(col_widths[j], row[j].length());
            }
         }
     }

     ostringstream oss;
     string separator = "+";
     for (size_t width : col_widths) {
         separator += string(width + 2, '-') + "+"; // +2 for padding
     }
     separator += "\n";

     oss << separator;

     // Header row
     if (!header.empty()) {
         oss << "|";
         for (size_t j = 0; j < num_cols; ++j) {
             string cell = (j < header.size()) ? header[j] : "";
             oss << " " << left << setw(col_widths[j]) << cell << " |";
         }
         oss << "\n";
         oss << separator;
     }

     // Data rows
     for (const auto& row : data) {
         oss << "|";
         for (size_t j = 0; j < num_cols; ++j) {
             string cell = (j < row.size()) ? row[j] : "";
              // Right-align state numbers and rule numbers if desired
              bool right_align = false;
              if (!header.empty() && j < header.size()) {
                  if (header[j] == "State") right_align = true;
                  if (cell.length() > 1 && (cell[0] == 'r' || cell[0] == 'S') && all_of(cell.begin() + 1, cell.end(), ::isdigit)) {
                     // Maybe right-align S/r actions slightly differently? For now, left.
                  } else if (all_of(cell.begin(), cell.end(), ::isdigit)) {
                       if(header[j] != "Input Ptr") // Keep input ptr left aligned
                           right_align = true;
                  }
              }

              if (right_align) {
                   oss << " " << right << setw(col_widths[j]) << cell << " |";
              } else {
                   oss << " " << left << setw(col_widths[j]) << cell << " |";
              }
         }
         oss << "\n";
     }

     oss << separator;
     return oss.str();
}

// Helper to print states clearly
void print_clr1_state(int state_id, const vector<Clr1Item>& state) {
    cout << "State " << state_id << ":\n";
    if (state.empty()) {
        cout << "  (empty)\n";
        return;
    }
    for (const auto& item : state) {
        cout << "  [" << item.first << ", " << item.second << "]\n";
    }
}


// --- Main Function ---
int main() {
    try {
        cout << "CLR(1) Parser Generator and Parser\n";
        cout << "===================================\n";
        cout << "Note: Use '" << EPSILON << "' to represent epsilon productions (e.g., A->" << EPSILON << ").\n";

        int grammar_num;
        cout << "Enter grammar number (e.g., 1 for grammar/1.txt): ";
        cin >> grammar_num;
        cin.ignore(numeric_limits<streamsize>::max(), '\n'); // Consume newline

        // --- Read Grammar ---
        string grammar_filename = "grammar/" + to_string(grammar_num) + ".txt";
        ifstream grammar_file(grammar_filename);
        if (!grammar_file) {
            cerr << "Error: Cannot open grammar file: " << grammar_filename << endl;
            return 1;
        }

        vector<string> original_grammar;
        string line;
        cout << "\nReading Grammar from " << grammar_filename << ":\n";
        while (getline(grammar_file, line)) {
            // Basic trim
            line.erase(0, line.find_first_not_of(" \t\n\r\f\v"));
            line.erase(line.find_last_not_of(" \t\n\r\f\v") + 1);
            if (!line.empty() && line.rfind("//", 0) != 0) { // Ignore empty lines and comments starting with //
                original_grammar.push_back(line);
                cout << "  " << line << endl;
            }
        }
        grammar_file.close();

        if (original_grammar.empty()) {
             cerr << "Error: Grammar file is empty or contains no valid productions." << endl;
             return 1;
        }

        // --- Augment Grammar ---
        if (!isupper(original_grammar[0][0])) {
             cerr << "Error: First rule's LHS must be an uppercase non-terminal (start symbol)." << endl;
             return 1;
        }
        string start_symbol_str(1, original_grammar[0][0]);
        string augmented_start_rule_no_dot = "X->" + start_symbol_str; // Use a distinct start symbol 'X'
        // We don't physically add X->S to the grammar list used for FIRST/Closure/GOTO,
        // but we use it to bootstrap the process. The original grammar list is passed around.

        cout << "\nAugmented Start Rule (for initial state): " << augmented_start_rule_no_dot << " (Lookahead: $)" << endl;
        cout << "---------------------------------------------------------------\n";

        // --- Compute Terminals, Non-Terminals, and FIRST Sets ---
        cout << "Computing Terminals, Non-Terminals, and FIRST sets...\n";
        set<char> terminals = get_terminals(original_grammar);
        set<char> non_terminals = get_non_terminals(original_grammar);
        // Add the augmented start symbol 'X' to non-terminals *conceptually* if needed,
        // though it doesn't participate in FIRST sets directly in this implementation.
        // non_terminals.insert('X'); // Usually not needed for FIRST calc

        if (terminals.count(EPSILON)) {
            cout << "Info: Epsilon ('" << EPSILON << "') found as a terminal/production RHS.\n";
        } else {
             cout << "Info: Epsilon ('" << EPSILON << "') not explicitly found. Assuming non-epsilon grammar unless rules like A-> exist.\n";
        }


        map<char, set<char>> first_sets = compute_first_sets(original_grammar, non_terminals, terminals);

        cout << "\nFIRST Sets:\n";
        for(char nt : non_terminals) {
            cout << "  FIRST(" << nt << ") = { ";
            string delim = "";
            for(char f : first_sets[nt]) { cout << delim << f; delim = ", "; }
            cout << " }\n";
        }
         cout << "---------------------------------------------------------------\n";


        // --- Generate States and DFA ---
        cout << "Generating CLR(1) States (Canonical Collection)...\n";
        vector<vector<Clr1Item>> canonical_collection;
        map<int, map<char, int>> dfa_goto;
        generate_states_and_dfa(original_grammar, augmented_start_rule_no_dot, first_sets, non_terminals,
                                canonical_collection, dfa_goto);

        cout << "Generated " << canonical_collection.size() << " states.\n";
        cout << "\nCanonical Collection of CLR(1) Item Sets:\n";
        for (size_t i = 0; i < canonical_collection.size(); ++i) {
            print_clr1_state(i, canonical_collection[i]);
        }
         cout << "---------------------------------------------------------------\n";


        // --- Build Parsing Table ---
         cout << "Building CLR(1) Action and Goto Tables...\n";
        map<int, map<char, string>> action_table;
        map<int, map<char, int>> goto_table;
        build_parsing_table(canonical_collection, dfa_goto, original_grammar, augmented_start_rule_no_dot,
                             terminals, non_terminals, action_table, goto_table);

        // --- Display Parsing Table ---
        vector<string> terminals_sorted;
        for (char t : terminals) terminals_sorted.push_back(string(1, t));
        sort(terminals_sorted.begin(), terminals_sorted.end());

        vector<string> non_terminals_sorted;
        for(char nt : non_terminals) non_terminals_sorted.push_back(string(1, nt));
        sort(non_terminals_sorted.begin(), non_terminals_sorted.end());


        vector<string> header = {"State"};
        // Add Action columns (terminals)
        header.insert(header.end(), terminals_sorted.begin(), terminals_sorted.end());
        // Add Goto columns (non-terminals)
        header.insert(header.end(), non_terminals_sorted.begin(), non_terminals_sorted.end());

         vector<vector<string>> table_data;
         for (int i = 0; i < canonical_collection.size(); ++i) {
             vector<string> row;
             row.push_back(to_string(i));
             // Action Part
             for (const string& term_str : terminals_sorted) {
                  char term = term_str[0];
                 if (action_table.count(i) && action_table.at(i).count(term)) {
                     row.push_back(action_table.at(i).at(term));
                 } else {
                     row.push_back(""); // Empty cell
                 }
             }
             // Goto Part
             for (const string& non_term_str : non_terminals_sorted) {
                 char non_term = non_term_str[0];
                  if (goto_table.count(i) && goto_table.at(i).count(non_term)) {
                      row.push_back(to_string(goto_table.at(i).at(non_term)));
                  } else {
                      row.push_back(""); // Empty cell
                  }
             }
             table_data.push_back(row);
         }

         cout << "\nCLR(1) Parsing Table (Action | Goto):\n";
         string table_string = format_table_to_string(table_data, header);
         cout << table_string;
         cout << "---------------------------------------------------------------\n";


        // --- Parse Input String ---
        cout << "Enter the string to be parsed (without $): ";
        string input_string;
        getline(cin, input_string); // Read the whole line

        // Basic trim again
        input_string.erase(0, input_string.find_first_not_of(" \t\n\r\f\v"));
        input_string.erase(input_string.find_last_not_of(" \t\n\r\f\v") + 1);

        string input_with_dollar = input_string + "$";
        cout << "Parsing input: " << input_with_dollar << "\n\n";

        vector<vector<string>> parse_steps;
        bool accepted = parse_input(input_with_dollar, action_table, goto_table, original_grammar, parse_steps);

        // --- Display Parsing Steps ---
        vector<string> parse_header = {"Action/Reduce", "Input Ptr", "Lookahead", "Stack"};
        string parsing_steps_table = format_table_to_string(parse_steps, parse_header);
        cout << "Parsing Steps:\n";
        cout << parsing_steps_table;
        cout << "---------------------------------------------------------------\n";


        // --- Report Result & Save ---
        string file_content_to_save;
        file_content_to_save += "Grammar File: " + grammar_filename + "\n";
        file_content_to_save += "Input String: " + input_string + "\n\n";
        file_content_to_save += "CLR(1) Parsing Table:\n";
        file_content_to_save += table_string + "\n";
        file_content_to_save += "Parsing Steps:\n";
        file_content_to_save += parsing_steps_table + "\n";


        if (accepted) {
            cout << "Result: SUCCESS! String \"" << input_string << "\" is accepted by the grammar.\n";
            file_content_to_save += "Result: ACCEPTED\n";
            string compressed_name = compress_name(input_string);
            string filename_suffix = compressed_name.empty() ? "accepted_string" : compressed_name;
            save_file(file_content_to_save, grammar_num, filename_suffix);
        } else {
            cout << "Result: FAILURE! String \"" << input_string << "\" is rejected by the grammar.\n";
            file_content_to_save += "Result: REJECTED\n";
             string compressed_name = compress_name(input_string);
             string filename_suffix = (compressed_name.empty() ? "rejected_string" : compressed_name) + "_rejected";
             save_file(file_content_to_save, grammar_num, filename_suffix);
        }

    } catch (const fs::filesystem_error& e) {
        cerr << "\nFilesystem Error: " << e.what() << endl;
        cerr << "Please ensure the 'grammar' directory exists and contains the required file." << endl;
        cerr << "Also check permissions for creating the 'parsable_strings' directory." << endl;
        return 1;
    } catch (const runtime_error& e) {
        cerr << "\nRuntime Error: " << e.what() << endl;
         if (string(e.what()).find("Grammar is not CLR(1)") != string::npos) {
             cerr << "The provided grammar cannot be parsed using a CLR(1) parser due to conflicts." << endl;
             cerr << "Consider using LALR(1) or checking the grammar rules." << endl;
         } else if (string(e.what()).find("Stack underflow") != string::npos || string(e.what()).find("Invalid rule") != string::npos) {
              cerr << "An internal error occurred during parsing, possibly related to table generation or input." << endl;
         }
        return 1;
    } catch (const exception& e) {
        cerr << "\nAn unexpected error occurred: " << e.what() << endl;
        return 1;
    } catch (...) {
        cerr << "\nAn unknown error occurred." << endl;
        return 1;
    }

    return 0;
}