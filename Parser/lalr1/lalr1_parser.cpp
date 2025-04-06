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
#include <iomanip> 
#include <limits>

using namespace std;
namespace fs = std::filesystem;

// Type alias for CLR(1) item: { rule_with_dot, lookahead_char }
using Clr1Item = pair<string, char>;
// Type alias for LALR(1) item: { rule_with_dot, set_of_lookahead_chars }
using Lalr1Item = pair<string, set<char>>;

const char EPSILON = '@'; // Define a character to represent epsilon

// --- Helper Functions (Mostly unchanged, some adapted for LALR(1) printing) ---

// Replaces "->" with "->."
string add_dot_after_arrow(const string &production) {
    size_t arrow_pos = production.find("->");
    if (arrow_pos == string::npos) {
        return "." + production; // Should not happen with valid grammar
    }
    string modified_prod = production;
    modified_prod.insert(arrow_pos + 2, ".");
    return modified_prod;
}

// Sorts CLR(1) items within a state for canonical representation
vector<Clr1Item> get_sorted_clr1_state(const vector<Clr1Item>& state) {
    vector<Clr1Item> sorted_state = state;
    sort(sorted_state.begin(), sorted_state.end()); // Default pair comparison works
    return sorted_state;
}

// Sorts LALR(1) items within a state for canonical representation
vector<Lalr1Item> get_sorted_lalr1_state(const vector<Lalr1Item>& state) {
    vector<Lalr1Item> sorted_state = state;
    // Sort primarily by rule string, secondarily by lookahead set
    sort(sorted_state.begin(), sorted_state.end(),
        [](const Lalr1Item& a, const Lalr1Item& b) {
            if (a.first != b.first) {
                return a.first < b.first;
            }
            // Compare sets element by element (lexicographically)
            return a.second < b.second;
        });
    return sorted_state;
}

// Helper to get the kernel (set of rule strings) from a CLR(1) state
set<string> get_clr1_state_kernel(const vector<Clr1Item>& state) {
    set<string> kernel;
    for (const auto& item : state) {
        kernel.insert(item.first);
    }
    return kernel;
}


// Function: get_terminals (Unchanged)
set<char> get_terminals(const vector<string>& gram) {
    set<char> terms;
    for (const string& p : gram) {
        size_t arrowPos = p.find("->");
        if (arrowPos == string::npos) continue;
        string right = p.substr(arrowPos + 2);
        for (char t : right) {
            if (!isupper(t) && t != '.' && t != '\0' && t != EPSILON) { // Exclude epsilon here too
                terms.insert(t);
            }
        }
    }
    terms.insert('$'); // Add end-of-input marker
    return terms;
}

// Function: get_non_terminals (Unchanged)
set<char> get_non_terminals(const vector<string>& gram) {
    set<char> non_terms;
    for (const string& p : gram) {
        size_t arrowPos = p.find("->");
        if (arrowPos != string::npos && arrowPos > 0 && isupper(p[0])) {
            non_terms.insert(p[0]);
        }
        if (arrowPos != string::npos) {
             string right = p.substr(arrowPos + 2);
             for (char t : right) {
                 if (isupper(t)) {
                     non_terms.insert(t);
                 }
             }
        }
    }
     if (!gram.empty()) {
         size_t arrowPosFirst = gram[0].find("->");
         if(arrowPosFirst != string::npos && arrowPosFirst > 0 && isupper(gram[0][0])) {
              non_terms.insert(gram[0][0]);
         }
     }
    return non_terms;
}


// --- FIRST Set Computation (Unchanged) ---
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
                 cerr << "Warning: FIRST set not found for non-terminal '" << symbol << "'" << endl;
            }
        } else if (symbol == EPSILON) {
            symbol_first.insert(EPSILON);
        }
         else { // Terminal or $
            symbol_first.insert(symbol);
        }

        for (char f : symbol_first) {
            if (f != EPSILON) {
                result.insert(f);
            }
        }
        if (symbol_first.find(EPSILON) == symbol_first.end()) {
            all_derive_epsilon = false;
            break;
        }
    }

    if (all_derive_epsilon) {
        result.insert(EPSILON);
    }
    return result;
}

map<char, set<char>> compute_first_sets(const vector<string>& grammar_productions, const set<char>& non_terminals, const set<char>& terminals) {
    map<char, set<char>> first_sets;
    for (char t : terminals) first_sets[t].insert(t);
    first_sets[EPSILON].insert(EPSILON);
    first_sets['$'].insert('$');
    for (char nt : non_terminals) first_sets[nt] = set<char>();

    bool changed = true;
    while (changed) {
        changed = false;
        for (const string& prod : grammar_productions) {
            size_t arrow_pos = prod.find("->");
            if (arrow_pos == string::npos || arrow_pos == 0) continue;
            char lhs = prod[0];
            if (!non_terminals.count(lhs)) continue;
            string rhs = prod.substr(arrow_pos + 2);
            if (rhs.empty() || rhs == string(1, EPSILON)) { // Handle empty and explicit epsilon
                 rhs = string(1, EPSILON); // Represent internally as EPSILON char
            }

            set<char> rhs_first = first_of_sequence(rhs, first_sets, non_terminals);
            size_t old_size = first_sets[lhs].size();
            first_sets[lhs].insert(rhs_first.begin(), rhs_first.end());
            if (first_sets[lhs].size() > old_size) {
                changed = true;
            }
        }
    }
    return first_sets;
}


// --- Core CLR(1) Functions (Used to generate initial states before merging) ---

// Function: closure (Unchanged from CLR(1) version)
vector<Clr1Item> closure(const vector<Clr1Item>& initial_items,
                         const vector<string>& grammar_productions,
                         const map<char, set<char>>& first_sets,
                         const set<char>& non_terminals)
{
    vector<Clr1Item> current_closure = initial_items;
    vector<Clr1Item> worklist = initial_items;
    set<Clr1Item> closure_set(initial_items.begin(), initial_items.end());
    int processed_count = 0;

    while(processed_count < worklist.size()){
        Clr1Item item = worklist[processed_count++];
        string rule = item.first;
        char lookahead = item.second;
        size_t dot_pos = rule.find('.');

        if (dot_pos != string::npos && dot_pos + 1 < rule.size()) {
            char symbol_after_dot = rule[dot_pos + 1];
            if (non_terminals.count(symbol_after_dot)) {
                string sequence_after_B;
                if (dot_pos + 2 < rule.size()) {
                    sequence_after_B = rule.substr(dot_pos + 2);
                }
                // Calculate FIRST(beta + a) where item is [A -> alpha . B beta, a]
                // We need FIRST(beta + original_lookahead)
                string sequence_for_first = sequence_after_B;
                // If sequence_after_B is empty, represents epsilon.
                // first_of_sequence needs the lookahead appended.
                sequence_for_first += lookahead; // Append original lookahead

                set<char> lookaheads_for_new_items = first_of_sequence(sequence_for_first, first_sets, non_terminals);


                for (const string& prod : grammar_productions) {
                    // Check if production starts with the symbol after the dot (B)
                    size_t arrow_pos_prod = prod.find("->");
                     // Ensure prod is valid and LHS matches symbol_after_dot
                    if (arrow_pos_prod != string::npos && arrow_pos_prod > 0 && prod[0] == symbol_after_dot) {
                        string new_item_dotted = add_dot_after_arrow(prod);
                        for (char b : lookaheads_for_new_items) {
                            if (b == EPSILON) continue; // Epsilon isn't a lookahead terminal
                             Clr1Item new_item = {new_item_dotted, b};
                             if (closure_set.find(new_item) == closure_set.end()) {
                                 closure_set.insert(new_item);
                                 current_closure.push_back(new_item);
                                 worklist.push_back(new_item);
                             }
                        }
                    }
                }
            }
        }
    }
    return get_sorted_clr1_state(current_closure); // Sort CLR(1) state
}

// Function: goto_set (Unchanged from CLR(1) version)
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
                string next_rule = rule;
                swap(next_rule[dot_pos], next_rule[dot_pos + 1]);
                kernel_items.push_back({next_rule, lookahead});
            }
        }
    }
    // Compute closure only if kernel_items is not empty
    if (kernel_items.empty()) {
        return {}; // Return empty vector if no items move the dot over 'symbol'
    }
    return closure(kernel_items, grammar_productions, first_sets, non_terminals);
}


// Function: generate_clr1_states_and_dfa
// Generates the CLR(1) states and DFA (needed before merging for LALR(1)).
void generate_clr1_states_and_dfa(
    const vector<string>& grammar_productions,
    const string& augmented_start_rule,
    const map<char, set<char>>& first_sets,
    const set<char>& non_terminals,
    vector<vector<Clr1Item>>& canonical_collection_clr1, // Output: CLR(1) states
    map<int, map<char, int>>& dfa_goto_clr1              // Output: CLR(1) transitions
) {
    canonical_collection_clr1.clear();
    dfa_goto_clr1.clear();
    map<vector<Clr1Item>, int> state_to_id; // Map sorted CLR(1) state to its ID
    vector<vector<Clr1Item>> states_to_process;

    string start_item_rule = add_dot_after_arrow(augmented_start_rule);
    Clr1Item initial_clr_item = {start_item_rule, '$'};
    vector<Clr1Item> initial_state_items = closure({initial_clr_item}, grammar_productions, first_sets, non_terminals);

    canonical_collection_clr1.push_back(initial_state_items);
    state_to_id[initial_state_items] = 0;
    states_to_process.push_back(initial_state_items);
    int current_id = 0;

    while (current_id < states_to_process.size()) {
        vector<Clr1Item> current_state_items = states_to_process[current_id];
        int from_state_id = state_to_id[current_state_items]; // Should be current_id

        set<char> possible_symbols;
        for (const Clr1Item& item : current_state_items) {
            const string& rule = item.first;
            size_t dot_pos = rule.find('.');
            if (dot_pos != string::npos && dot_pos + 1 < rule.size()) {
                possible_symbols.insert(rule[dot_pos + 1]);
            }
        }

        for (char symbol : possible_symbols) {
             if (symbol == EPSILON) continue; // Cannot transition on epsilon itself
            vector<Clr1Item> next_state_items = goto_set(current_state_items, symbol, grammar_productions, first_sets, non_terminals);

            if (!next_state_items.empty()) { // Only process if goto leads to a valid state
                // next_state_items is already sorted by closure/goto
                if (state_to_id.find(next_state_items) == state_to_id.end()) {
                    // New state found
                    int new_state_id = canonical_collection_clr1.size();
                    state_to_id[next_state_items] = new_state_id;
                    canonical_collection_clr1.push_back(next_state_items);
                    states_to_process.push_back(next_state_items); // Add to worklist
                    dfa_goto_clr1[from_state_id][symbol] = new_state_id;
                } else {
                    // Existing state
                    int existing_state_id = state_to_id[next_state_items];
                    dfa_goto_clr1[from_state_id][symbol] = existing_state_id;
                }
            }
        }
        current_id++;
    }
}


// --- LALR(1) Specific Functions ---

// Function: merge_clr1_states_for_lalr1
// Merges CLR(1) states with identical kernels to create LALR(1) states and transitions.
void merge_clr1_states_for_lalr1(
    const vector<vector<Clr1Item>>& canonical_collection_clr1, // Input: CLR(1) states
    const map<int, map<char, int>>& dfa_goto_clr1,             // Input: CLR(1) transitions
    vector<vector<Lalr1Item>>& canonical_collection_lalr1,     // Output: LALR(1) states
    map<int, map<char, int>>& dfa_goto_lalr1,                  // Output: LALR(1) transitions
    map<int, int>& map_clr1_to_lalr1_id                       // Output: Mapping CLR(1) state ID -> LALR(1) state ID
) {
    canonical_collection_lalr1.clear();
    dfa_goto_lalr1.clear();
    map_clr1_to_lalr1_id.clear();

    // 1. Group CLR(1) states by kernel
    map<set<string>, vector<int>> kernel_to_clr1_state_ids;
    for (size_t i = 0; i < canonical_collection_clr1.size(); ++i) {
        set<string> kernel = get_clr1_state_kernel(canonical_collection_clr1[i]);
        // Ensure kernel is not empty before adding (shouldn't happen for valid states)
        if (!kernel.empty()) {
             kernel_to_clr1_state_ids[kernel].push_back(i);
        } else if (!canonical_collection_clr1[i].empty()){
             // If state is not empty but kernel is, indicates an issue (e.g., item format error)
             cerr << "Warning: CLR(1) state " << i << " has items but yields an empty kernel." << endl;
        }
    }

    // 2. Create LALR(1) states by merging lookaheads
    // We need a stable way to map merged LALR state content to its final ID
    // Let's build the states first, then assign IDs based on final order
    vector<vector<Lalr1Item>> temp_lalr1_states;
    map<set<string>, int> kernel_to_temp_lalr1_index; // Map kernel to index in temp_lalr1_states

    for (const auto& pair : kernel_to_clr1_state_ids) {
        const set<string>& kernel = pair.first;
        const vector<int>& clr1_ids_in_group = pair.second;
        map<string, set<char>> merged_items; // rule_with_dot -> set<lookahead>

        for (int clr1_id : clr1_ids_in_group) {
            for (const auto& clr1_item : canonical_collection_clr1[clr1_id]) {
                merged_items[clr1_item.first].insert(clr1_item.second);
            }
        }

        vector<Lalr1Item> lalr1_state_items;
        for (const auto& item_pair : merged_items) {
            lalr1_state_items.push_back({item_pair.first, item_pair.second});
        }
        lalr1_state_items = get_sorted_lalr1_state(lalr1_state_items);

        // Store the merged state temporarily and map kernel to its index
        kernel_to_temp_lalr1_index[kernel] = temp_lalr1_states.size();
        temp_lalr1_states.push_back(lalr1_state_items);

        // Update the mapping from CLR(1) IDs to this *temporary* LALR(1) index
        for (int clr1_id : clr1_ids_in_group) {
            // This map needs to store the final LALR ID, fill later
            // map_clr1_to_lalr1_id[clr1_id] = temporary_index;
        }
    }

    // Assign final IDs and populate the output collection and map
    // Sort temporary states maybe? No, the order should depend on the kernel grouping order.
    canonical_collection_lalr1 = temp_lalr1_states; // Assign collected states
    map<vector<Lalr1Item>, int> lalr1_state_to_final_id;
    for(size_t i=0; i < canonical_collection_lalr1.size(); ++i) {
        lalr1_state_to_final_id[canonical_collection_lalr1[i]] = i;
    }

    // Populate the clr1 -> lalr1 map using the final IDs
     for (const auto& pair : kernel_to_clr1_state_ids) {
        const set<string>& kernel = pair.first;
        const vector<int>& clr1_ids_in_group = pair.second;

        // Find the merged state corresponding to this kernel
         map<string, set<char>> merged_items;
         for (int clr1_id : clr1_ids_in_group) {
             for (const auto& clr1_item : canonical_collection_clr1[clr1_id]) {
                 merged_items[clr1_item.first].insert(clr1_item.second);
             }
         }
         vector<Lalr1Item> lalr1_state_items;
         for (const auto& item_pair : merged_items) {
             lalr1_state_items.push_back({item_pair.first, item_pair.second});
         }
         lalr1_state_items = get_sorted_lalr1_state(lalr1_state_items);

         // Get the final ID assigned to this merged state
         int final_lalr1_id = lalr1_state_to_final_id.at(lalr1_state_items);

         // Update the mapping for all CLR(1) states in this group
         for (int clr1_id : clr1_ids_in_group) {
            map_clr1_to_lalr1_id[clr1_id] = final_lalr1_id;
         }
    }


    // 3. Create LALR(1) GOTO transitions using the final IDs
    for (const auto& clr_trans_pair : dfa_goto_clr1) {
        int clr1_from_state = clr_trans_pair.first;
        // Ensure the from_state exists in the map (it should)
        if (map_clr1_to_lalr1_id.find(clr1_from_state) == map_clr1_to_lalr1_id.end()) {
             cerr << "Warning: CLR(1) state " << clr1_from_state << " not found in mapping during GOTO creation." << endl;
             continue;
        }
        int lalr1_from_state = map_clr1_to_lalr1_id.at(clr1_from_state);

        for (const auto& symbol_target_pair : clr_trans_pair.second) {
            char symbol = symbol_target_pair.first;
            int clr1_to_state = symbol_target_pair.second;

            // Ensure the to_state exists in the map
             if (map_clr1_to_lalr1_id.find(clr1_to_state) == map_clr1_to_lalr1_id.end()) {
                  cerr << "Warning: CLR(1) GOTO target state " << clr1_to_state << " not found in mapping for transition from " << clr1_from_state << " on '" << symbol << "'." << endl;
                  continue;
             }
            int lalr1_to_state = map_clr1_to_lalr1_id.at(clr1_to_state);

            // Check for inconsistencies (should not happen in LALR(1) merging)
            if (dfa_goto_lalr1.count(lalr1_from_state) && dfa_goto_lalr1[lalr1_from_state].count(symbol) && dfa_goto_lalr1[lalr1_from_state][symbol] != lalr1_to_state) {
                 // This indicates a potential issue if different CLR(1) transitions map to different LALR(1) transitions for the same merged state/symbol
                 throw runtime_error("LALR(1) GOTO inconsistency detected during merging for LALR state " + to_string(lalr1_from_state) + " on symbol '" + string(1, symbol) + "'. Targetting " + to_string(dfa_goto_lalr1[lalr1_from_state][symbol]) + " and " + to_string(lalr1_to_state) + ".");
            }
            dfa_goto_lalr1[lalr1_from_state][symbol] = lalr1_to_state;
        }
    }
}


// Function: build_lalr1_parsing_table
// Builds the LALR(1) Action and Goto tables. Throws if conflicts arise.
void build_lalr1_parsing_table(
    const vector<vector<Lalr1Item>>& canonical_collection_lalr1, // LALR(1) states
    const map<int, map<char, int>>& dfa_goto_lalr1,             // LALR(1) transitions
    const vector<string>& original_grammar,                     // Original rules (for reduce)
    const string& augmented_production_no_dot,                  // E.g., "X->S"
    const set<char>& terminals,                                 // Set of terminal symbols (inc '$')
    const set<char>& non_terminals,                             // Set of non-terminal symbols
    map<int, map<char, string>>& action_table,                  // Output: Action table
    map<int, map<char, int>>& goto_table                        // Output: Goto table
) {
    action_table.clear();
    goto_table.clear();

    // Populate GOTO table from LALR(1) DFA transitions on non-terminals
    for(const auto& [from_state, transitions] : dfa_goto_lalr1) {
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
    for (int i = 0; i < canonical_collection_lalr1.size(); ++i) {
        const vector<Lalr1Item>& state_items = canonical_collection_lalr1[i];

        // Handle Shifts first based on DFA transitions
        if (dfa_goto_lalr1.count(i)) {
            for (const auto& [symbol, target_state] : dfa_goto_lalr1.at(i)) {
                if (terminals.count(symbol)) { // Shift only on terminals
                    string shift_action = "S" + to_string(target_state);
                    // Check for existing action only if necessary (reduce added first below might be better)
                    // If we add shifts first, a later reduce might conflict.
                    action_table[i][symbol] = shift_action; // Tentatively add shift
                }
            }
        }

        // Handle Reduces and Accept
        for (const Lalr1Item& item : state_items) {
            string rule = item.first;
            const set<char>& lookaheads = item.second;
            size_t dot_pos = rule.find('.');
            if (dot_pos == string::npos || dot_pos + 1 < rule.size()) {
                // Not a reduce item (dot not at end) or invalid item
                continue;
            }

            // Item is of the form [A -> α ., {lookahead_set}]
            string production_rule = rule.substr(0, dot_pos); // Get rule without dot

            // Special case: Accept state [X -> S ., {'$'}]
            if (production_rule == augmented_production_no_dot) {
                 if (lookaheads.count('$')) { // Must have $ in lookahead set for accept
                    string accept_action = "Accept";
                    // Check for conflict for ACTION[i, '$']
                    if (action_table.count(i) && action_table[i].count('$')) {
                         const string& existing_action = action_table[i]['$'];
                         if (existing_action != accept_action) { // e.g., vs Shift or Reduce
                             throw runtime_error("Grammar is not LALR(1): Conflict (Accept/" + string(1,existing_action[0]) + ") in state " + to_string(i) + " on '$'. Existing: " + existing_action + ", New: Accept.");
                         }
                    } else {
                         action_table[i]['$'] = accept_action;
                    }
                }
                 // Ignore other lookaheads for the augmented rule end if any (shouldn't happen for valid start)
            }
            // Normal Reduce Action [A -> alpha ., {lookaheads}]
            else {
                if (!prod_num.count(production_rule)) {
                    cerr << "Warning: Could not find production number for reducing rule: " << production_rule << endl;
                    continue; // Skip this item if rule not found
                }
                int rule_number = prod_num[production_rule];
                string reduce_action = "r" + to_string(rule_number);

                // Add reduce action for *EACH* lookahead in the set
                for (char lookahead : lookaheads) {
                     if (terminals.count(lookahead)) { // Ensure lookahead is a terminal or $
                        // Check for conflict for ACTION[i, lookahead]
                        if (action_table.count(i) && action_table[i].count(lookahead)) {
                             const string& existing_action = action_table[i][lookahead];
                             if (existing_action != reduce_action) {
                                 // Conflict detected! Could be Shift/Reduce or Reduce/Reduce.
                                 throw runtime_error(string("Grammar is not LALR(1): Conflict (") +
                                    (existing_action[0] == 'S' ? "Shift/Reduce" : "Reduce/Reduce") +
                                    ") in state " + std::to_string(i) + " on lookahead '" + lookahead +
                                    "'. Existing: " + existing_action + ", New: " + reduce_action +
                                    " (from item [" + rule + ",...])");
                             }
                             // else, action is the same reduce, no conflict (might happen if multiple items reduce on same rule/lookahead)
                         } else {
                             // No existing action for this lookahead, safe to add
                             action_table[i][lookahead] = reduce_action;
                         }
                    } else {
                        // Should only happen if '$' was not added to terminals correctly or invalid lookahead generated
                        if (lookahead != '$') {
                           cerr << "Warning: Invalid non-terminal lookahead '" << lookahead << "' found for item " << rule << " in state " << i << endl;
                        }
                        // Allow '$' even if not explicitly in computed terminals initially
                         else if (action_table.count(i) && action_table[i].count('$')) {
                              const string& existing_action = action_table[i]['$'];
                              if (existing_action != reduce_action) {
                                   throw runtime_error(string("Grammar is not LALR(1): Conflict (") +
                                    (existing_action[0] == 'S' ? "Shift/Reduce" : "Reduce/Reduce") +
                                    ") in state " + std::to_string(i) + " on lookahead '$'. Existing: " + existing_action + ", New: " + reduce_action +
                                    " (from item [" + rule + ",...])");
                              }
                         } else {
                             action_table[i]['$'] = reduce_action;
                         }
                    }
                } // End loop over lookaheads
            }
        } // End loop over items in state
    } // End loop over states
}


// --- Parsing ---

// Function: parse_input
bool parse_input(
    const string& input_string_with_dollar,
    const map<int, map<char, string>>& action_table,
    const map<int, map<char, int>>& goto_table,
    const vector<string>& original_grammar,
    vector<vector<string>>& parse_steps,
    int initial_state // *** MODIFIED: Added initial_state parameter ***
) {
    parse_steps.clear();
    vector<int> stack;
    // stack.push_back(0); // *** REMOVED: Hardcoded initial state ***
    stack.push_back(initial_state); // *** ADDED: Use correct initial state ***
    int input_ptr = 0;

    while (true) {
        if (stack.empty()) {
             vector<string> step = {"Error: Stack empty", to_string(input_ptr), "?", "[]"}; parse_steps.push_back(step); return false;
        }
        int current_state = stack.back();
        char lookahead = input_string_with_dollar[input_ptr];

        string action;
        bool action_found = false;
         // Check if current_state exists in the action table map
         auto state_action_it = action_table.find(current_state);
         if (state_action_it != action_table.end()) {
             // Check if lookahead exists for this state
             auto action_it = state_action_it->second.find(lookahead);
             if (action_it != state_action_it->second.end()) {
                 action = action_it->second;
                 action_found = true;
             }
         }


        if (!action_found) {
            vector<string> step = {"Error: No action", to_string(input_ptr), string(1, lookahead), ""};
            ostringstream stack_oss; stack_oss << "["; for(size_t j=0; j<stack.size(); ++j) stack_oss << stack[j] << (j == stack.size()-1 ? "" : ", "); stack_oss << "]"; step[3] = stack_oss.str();
            parse_steps.push_back(step);
            cerr << "Parse Error: No action defined for state " << current_state << " and lookahead '" << lookahead << "' at input position " << input_ptr << endl;
            return false;
        }

        vector<string> step = {action, to_string(input_ptr), string(1, lookahead), ""};
        ostringstream stack_oss; stack_oss << "["; for(size_t j=0; j<stack.size(); ++j) stack_oss << stack[j] << (j == stack.size()-1 ? "" : ", "); stack_oss << "]"; step[3] = stack_oss.str();
        parse_steps.push_back(step);

        if (action == "Accept") {
            return true;
        } else if (action[0] == 'S') { // Shift
            int target_state = stoi(action.substr(1));
            stack.push_back(target_state);
            input_ptr++;
        } else if (action[0] == 'r') { // Reduce
            int rule_number = stoi(action.substr(1));
            if (rule_number < 1 || rule_number > original_grammar.size()) {
                 vector<string> err_step = {"Error: Invalid rule " + to_string(rule_number), to_string(input_ptr), string(1, lookahead), stack_oss.str()}; parse_steps.push_back(err_step);
                 throw runtime_error("Internal Error: Invalid rule number " + to_string(rule_number));
            }
            string production_rule = original_grammar[rule_number - 1];
            size_t arrow_pos = production_rule.find("->");
             if (arrow_pos == string::npos) {
                 vector<string> err_step = {"Error: Bad production '" + production_rule + "'", to_string(input_ptr), string(1, lookahead), stack_oss.str()}; parse_steps.push_back(err_step);
                 throw runtime_error("Internal Error: Invalid production format '" + production_rule + "'");
             }
            string rhs = production_rule.substr(arrow_pos + 2);
             int pop_count = 0;
             if (rhs != string(1, EPSILON)) { // Handle explicit epsilon representation
                 pop_count = rhs.length();
             }
            char lhs_non_terminal = production_rule[0];

             // Check stack size BEFORE popping
             if (stack.size() < (size_t)(pop_count + 1)) { // Need pop_count states + 1 state below them
                  vector<string> err_step = {"Error: Stack underflow on reduce", to_string(input_ptr), string(1, lookahead), stack_oss.str()};
                 parse_steps.push_back(err_step);
                 throw runtime_error("Internal Error: Stack underflow during reduce for rule " + production_rule + " (Stack size " + to_string(stack.size()) + ", popping " + to_string(pop_count) + ")");
             }

            for (int k = 0; k < pop_count; ++k) {
                 // Check before each pop (redundant given check above, but safer)
                 if (stack.empty()) {
                     vector<string> err_step = {"Error: Stack empty during multi-pop", to_string(input_ptr), string(1, lookahead), "[]"}; parse_steps.push_back(err_step);
                     throw runtime_error("Internal Error: Stack empty during pop sequence for reduce.");
                 }
                 stack.pop_back();
            }

             // Check stack is not empty AFTER popping (should be guaranteed by size check above)
             if (stack.empty()) {
                 vector<string> err_step = {"Error: Stack empty after pop", to_string(input_ptr), string(1, lookahead), "[]"}; parse_steps.push_back(err_step);
                 throw runtime_error("Internal Error: Stack empty after popping for reduce.");
             }
            int exposed_state = stack.back();

            bool goto_found = false;
            int goto_state = -1;
            // Check if exposed_state exists in goto_table
            auto goto_state_it = goto_table.find(exposed_state);
            if (goto_state_it != goto_table.end()) {
                // Check if lhs_non_terminal exists for this state
                auto goto_symbol_it = goto_state_it->second.find(lhs_non_terminal);
                if (goto_symbol_it != goto_state_it->second.end()) {
                    goto_state = goto_symbol_it->second;
                    goto_found = true;
                }
            }


            if (!goto_found) {
                vector<string> err_step = {"Error: Undefined GOTO(" + to_string(exposed_state) + ", " + string(1, lhs_non_terminal) + ")", to_string(input_ptr), string(1, lookahead), ""};
                 ostringstream err_stack_oss; err_stack_oss << "["; for(size_t j=0; j<stack.size(); ++j) err_stack_oss << stack[j] << (j == stack.size()-1 ? "" : ", "); err_stack_oss << "]"; err_step[3] = err_stack_oss.str();
                parse_steps.push_back(err_step);
                 cerr << "Parse Error: Undefined GOTO for state " << exposed_state << " and non-terminal '" << lhs_non_terminal << "'" << endl;
                return false;
            }
            stack.push_back(goto_state);
        } else {
             vector<string> err_step = {"Error: Unknown action '" + action + "'", to_string(input_ptr), string(1, lookahead), stack_oss.str()}; parse_steps.push_back(err_step);
             throw runtime_error("Internal Error: Unknown action type '" + action + "'");
        }
    }
}


// --- Utility Functions (Unchanged except print_state) ---

string compress_name(const string &name) {
    string comp_name;
    for (char c : name) { if (isalnum(c)) comp_name += c; else if (comp_name.length() > 0 && comp_name.back() != '_') comp_name += '_'; }
    if (!comp_name.empty() && comp_name.back() == '_') comp_name.pop_back();
    if (comp_name.length() > 50) comp_name = comp_name.substr(0, 50);
    return comp_name.empty() ? "default" : comp_name;
}

void save_file(const string &content, int grammar_num, const string &name_suffix) {
    try {
        string directory = "parsable_strings/" + to_string(grammar_num) + "/";
        fs::create_directories(directory);
        string filename = directory + name_suffix + "_lalr1.txt"; // Append _lalr1
        ofstream f(filename);
        if (!f) { cerr << "Error: Could not open file for writing: " << filename << endl; return; }
        f << content; f.close();
        cout << "Output saved to " << filename << "\n";
    } catch (const exception& e) { cerr << "Error saving file: " << e.what() << endl; }
}

string format_table_to_string(const vector<vector<string>>& data, const vector<string>& header) {
     if (header.empty() && data.empty()) return "Table is empty.\n";
     size_t num_cols = header.empty() ? (data.empty() ? 0 : data[0].size()) : header.size();
     if (num_cols == 0) return "Table has no columns.\n";
     vector<size_t> col_widths(num_cols, 0);
     for (size_t j = 0; j < num_cols; ++j) col_widths[j] = max(col_widths[j], (j < header.size() ? header[j].length() : 4));
     for (const auto& row : data) for (size_t j = 0; j < row.size(); ++j) if(j < num_cols) col_widths[j] = max(col_widths[j], row[j].length());
     ostringstream oss; string separator = "+"; for (size_t w : col_widths) separator += string(w + 2, '-') + "+"; separator += "\n"; oss << separator;
     if (!header.empty()) { oss << "|"; for (size_t j = 0; j < num_cols; ++j) oss << " " << left << setw(col_widths[j]) << (j < header.size() ? header[j] : "") << " |"; oss << "\n"; oss << separator; }
     for (const auto& row : data) { oss << "|"; for (size_t j = 0; j < num_cols; ++j) { string cell = (j < row.size()) ? row[j] : ""; bool right_align = false; if (!header.empty() && j < header.size() && header[j] == "State") right_align = true; else if (!cell.empty() && all_of(cell.begin() + (cell[0]=='S' || cell[0]=='r' ? 1:0), cell.end(), ::isdigit)) if(j==0 || (j > 0 && header[j] != "Input Ptr")) right_align = true; if(right_align) oss << " " << right << setw(col_widths[j]) << cell << " |"; else oss << " " << left << setw(col_widths[j]) << cell << " |"; } oss << "\n"; }
     oss << separator; return oss.str();
}

// Helper to print LALR(1) states clearly
void print_lalr1_state(int state_id, const vector<Lalr1Item>& state) {
    cout << "State " << state_id << ":\n";
    if (state.empty()) {
        cout << "  (empty)\n";
        return;
    }
    // Sort items within the state before printing for consistency
    vector<Lalr1Item> sorted_state = get_sorted_lalr1_state(state);
    for (const auto& item : sorted_state) {
        cout << "  [" << item.first << ", {";
        string delim = "";
        // Sort lookaheads for consistent printing
        vector<char> lookaheads(item.second.begin(), item.second.end());
        sort(lookaheads.begin(), lookaheads.end());
        for (char la : lookaheads) {
            cout << delim << la;
            delim = ",";
        }
        cout << "}]\n";
    }
}

int main() {
    try {
        cout << "LALR(1) Parser Generator and Parser\n"; // Changed Title
        cout << "====================================\n";
        cout << "Note: Use '" << EPSILON << "' to represent epsilon productions (e.g., A->" << EPSILON << ").\n";

        int grammar_num;
        cout << "Enter grammar number (e.g., 1 for grammar/1.txt): ";
        // Input validation
        while (!(cin >> grammar_num)) {
             cout << "Invalid input. Please enter an integer: ";
             cin.clear();
             cin.ignore(numeric_limits<streamsize>::max(), '\n');
        }
        cin.ignore(numeric_limits<streamsize>::max(), '\n');

        // --- Read Grammar ---
        string grammar_filename = "grammar/" + to_string(grammar_num) + ".txt";
        ifstream grammar_file(grammar_filename);
        if (!grammar_file) { cerr << "Error: Cannot open grammar file: " << grammar_filename << endl; return 1; }
        vector<string> original_grammar;
        string line;
        cout << "\nReading Grammar from " << grammar_filename << ":\n";
        while (getline(grammar_file, line)) {
            line.erase(0, line.find_first_not_of(" \t\n\r\f\v"));
            line.erase(line.find_last_not_of(" \t\n\r\f\v") + 1);
            if (!line.empty() && line.rfind("//", 0) != 0) {
                original_grammar.push_back(line);
                cout << "  " << line << endl;
            }
        }
        grammar_file.close();
        if (original_grammar.empty()) { cerr << "Error: Grammar file is empty or contains no valid productions." << endl; return 1; }

        // --- Augment Grammar ---
        if (!isupper(original_grammar[0][0])) { cerr << "Error: First rule's LHS must be start symbol (uppercase)." << endl; return 1; }
        string start_symbol_str(1, original_grammar[0][0]);
        string augmented_start_rule_no_dot = "X->" + start_symbol_str; // Use a distinct start symbol 'X'
        cout << "\nAugmented Start Rule (for initial state): " << augmented_start_rule_no_dot << " (Lookahead: $)" << endl;
        cout << "---------------------------------------------------------------\n";

        // --- Compute Terminals, Non-Terminals, and FIRST Sets ---
        cout << "Computing Terminals, Non-Terminals, and FIRST sets...\n";
        set<char> terminals = get_terminals(original_grammar);
        set<char> non_terminals = get_non_terminals(original_grammar);
        map<char, set<char>> first_sets = compute_first_sets(original_grammar, non_terminals, terminals);
        cout << "\nFIRST Sets:\n";
        vector<char> nt_sorted(non_terminals.begin(), non_terminals.end()); sort(nt_sorted.begin(), nt_sorted.end());
        for(char nt : nt_sorted) {
            cout << "  FIRST(" << nt << ") = { "; string delim = "";
            vector<char> f_sorted(first_sets[nt].begin(), first_sets[nt].end()); sort(f_sorted.begin(), f_sorted.end());
            for(char f : f_sorted) { cout << delim << f; delim = ", "; } cout << " }\n";
        }
        cout << "---------------------------------------------------------------\n";

        // --- Generate CLR(1) States and DFA (Intermediate Step) ---
        cout << "Generating initial CLR(1) states and DFA...\n";
        vector<vector<Clr1Item>> canonical_collection_clr1;
        map<int, map<char, int>> dfa_goto_clr1;
        generate_clr1_states_and_dfa(original_grammar, augmented_start_rule_no_dot, first_sets, non_terminals,
                                     canonical_collection_clr1, dfa_goto_clr1);
        cout << "Generated " << canonical_collection_clr1.size() << " initial CLR(1) states.\n";
        cout << "---------------------------------------------------------------\n";


        // --- Merge CLR(1) states into LALR(1) states ---
        cout << "Merging CLR(1) states into LALR(1) states...\n";
        vector<vector<Lalr1Item>> canonical_collection_lalr1;
        map<int, map<char, int>> dfa_goto_lalr1;
        map<int, int> map_clr1_to_lalr1_id;
        merge_clr1_states_for_lalr1(canonical_collection_clr1, dfa_goto_clr1,
                                    canonical_collection_lalr1, dfa_goto_lalr1, map_clr1_to_lalr1_id);
        cout << "Merged into " << canonical_collection_lalr1.size() << " LALR(1) states.\n";

        // *** ADDED: Find and print the initial LALR state ID ***
        int initial_lalr1_state_id = -1;
        if (map_clr1_to_lalr1_id.count(0)) { // CLR(1) state 0 is always the initial one
            initial_lalr1_state_id = map_clr1_to_lalr1_id.at(0);
             cout << "Initial LALR(1) State ID (maps from CLR(1) state 0): " << initial_lalr1_state_id << endl;
        } else if (!canonical_collection_clr1.empty()) { // Only error if CLR states were generated
             cerr << "Critical Error: Cannot find LALR(1) state mapping for initial CLR(1) state 0." << endl;
             return 1; // Cannot proceed without initial state
        } else {
             cerr << "Warning: No CLR(1) states generated, cannot determine initial LALR(1) state." << endl;
             // Allow continuing if grammar was empty, table building will likely fail gracefully.
             initial_lalr1_state_id = 0; // Default guess, likely incorrect
        }
         // *** END ADDED ***


        // --- Print LALR(1) Item Sets ---
        cout << "\nCanonical Collection of LALR(1) Item Sets:\n";
        for (size_t i = 0; i < canonical_collection_lalr1.size(); ++i) {
            print_lalr1_state(i, canonical_collection_lalr1[i]);
        }
        cout << "---------------------------------------------------------------\n";


        // --- Build LALR(1) Parsing Table ---
        cout << "Building LALR(1) Action and Goto Tables...\n";
        map<int, map<char, string>> action_table;
        map<int, map<char, int>> goto_table;
        build_lalr1_parsing_table(canonical_collection_lalr1, dfa_goto_lalr1, original_grammar, augmented_start_rule_no_dot,
                                   terminals, non_terminals, action_table, goto_table);


        // --- Display Parsing Table ---
        vector<string> terminals_sorted; for (char t : terminals) terminals_sorted.push_back(string(1, t)); sort(terminals_sorted.begin(), terminals_sorted.end());
        vector<string> non_terminals_sorted; for(char nt : non_terminals) non_terminals_sorted.push_back(string(1, nt)); sort(non_terminals_sorted.begin(), non_terminals_sorted.end());
        vector<string> header = {"State"}; header.insert(header.end(), terminals_sorted.begin(), terminals_sorted.end()); header.insert(header.end(), non_terminals_sorted.begin(), non_terminals_sorted.end());
        vector<vector<string>> table_data;
        for (int i = 0; i < canonical_collection_lalr1.size(); ++i) {
             vector<string> row; row.push_back(to_string(i));
             for (const string& term_str : terminals_sorted) { char term = term_str[0]; row.push_back(action_table.count(i) && action_table.at(i).count(term) ? action_table.at(i).at(term) : ""); }
             for (const string& non_term_str : non_terminals_sorted) { char non_term = non_term_str[0]; row.push_back(goto_table.count(i) && goto_table.at(i).count(non_term) ? to_string(goto_table.at(i).at(non_term)) : ""); }
             table_data.push_back(row);
        }
        cout << "\nLALR(1) Parsing Table (Action | Goto):\n";
        string table_string = format_table_to_string(table_data, header);
        cout << table_string;
        cout << "---------------------------------------------------------------\n";


        // --- Parse Input String ---
        cout << "Enter the string to be parsed (without $): ";
        string input_string;
        getline(cin, input_string);
        input_string.erase(0, input_string.find_first_not_of(" \t\n\r\f\v")); input_string.erase(input_string.find_last_not_of(" \t\n\r\f\v") + 1);
        string input_with_dollar = input_string + "$";
        cout << "Parsing input: " << input_with_dollar << "\n\n";

        vector<vector<string>> parse_steps;
        // *** MODIFIED: Pass initial_lalr1_state_id to parse_input ***
        bool accepted = parse_input(input_with_dollar, action_table, goto_table, original_grammar, parse_steps, initial_lalr1_state_id);

        // --- Display Parsing Steps ---
        vector<string> parse_header = {"Action/Reduce", "Input Ptr", "Lookahead", "Stack"};
        string parsing_steps_table = format_table_to_string(parse_steps, parse_header);
        cout << "Parsing Steps:\n"; cout << parsing_steps_table;
        cout << "---------------------------------------------------------------\n";


        // --- Report Result & Save ---
        string file_content_to_save; file_content_to_save += "Grammar File: " + grammar_filename + "\n"; file_content_to_save += "Input String: " + input_string + "\n\n"; file_content_to_save += "LALR(1) Parsing Table:\n"; file_content_to_save += table_string + "\n"; file_content_to_save += "Parsing Steps:\n"; file_content_to_save += parsing_steps_table + "\n";
        string file_suffix;
        if (accepted) {
            cout << "Result: SUCCESS! String \"" << input_string << "\" is accepted by the LALR(1) grammar.\n"; file_content_to_save += "Result: ACCEPTED\n";
            file_suffix = compress_name(input_string);
        } else {
            cout << "Result: FAILURE! String \"" << input_string << "\" is rejected by the LALR(1) grammar.\n"; file_content_to_save += "Result: REJECTED\n";
             file_suffix = compress_name(input_string) + "_rejected";
        }
        save_file(file_content_to_save, grammar_num, file_suffix); // Save function appends _lalr1.txt

    } catch (const fs::filesystem_error& e) {
        cerr << "\nFilesystem Error: " << e.what() << endl;
        cerr << "Please ensure the 'grammar' directory exists and contains the required file." << endl;
        cerr << "Also check permissions for creating the 'parsable_strings' directory." << endl;
        return 1;
    } catch (const runtime_error& e) {
        cerr << "\nRuntime Error: " << e.what() << endl;
         if (string(e.what()).find("Grammar is not LALR(1)") != string::npos) {
             cerr << "The provided grammar cannot be parsed using an LALR(1) parser due to conflicts." << endl;
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