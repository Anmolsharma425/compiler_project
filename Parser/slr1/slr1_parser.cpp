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

using namespace std;
namespace fs = std::filesystem;

const char EPSILON_CHAR = '#';

// --- Helper Functions ---

// Replaces "->" with "->."
string add_dot_after_arrow(const string &production) {
    size_t arrow_pos = production.find("->");
    if (arrow_pos == string::npos) return production;
    string modified_prod = production;
    modified_prod.insert(arrow_pos + 2, ".");
    return modified_prod;
}

vector<string> get_sorted_state(const vector<string>& state) {
    vector<string> sorted_state = state;
    sort(sorted_state.begin(), sorted_state.end());
    return sorted_state;
}

set<char> get_non_terminals(const vector<string>& gram);
set<char> get_terminals(const vector<string>& gram);

set<char> get_terminals(const vector<string>& gram) {
    set<char> terms;
    for (const string& p : gram) {
        size_t arrowPos = p.find("->");
        if (arrowPos == string::npos) continue;
        string right = p.substr(arrowPos + 2);
        for (char t : right) {
            // Terminal if not uppercase and not the designated epsilon character
            if (!isupper(t) && t != EPSILON_CHAR && t != '\0') {
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
         // Add LHS non-terminal
         if (arrowPos != string::npos && arrowPos > 0 && isupper(p[0])) {
             non_terms.insert(p[0]);
         }
         // Add RHS non-terminals
        if (arrowPos != string::npos) {
            string right = p.substr(arrowPos + 2);
            for (char t : right) {
                if (isupper(t)) {
                    non_terms.insert(t);
                }
            }
        }
    }
    return non_terms;
}


// --- Core LR(0) State Generation (Used by SLR(1)) ---

// Function: closure
vector<string> closure(const vector<string>& initial_items, const vector<string>& grammar_productions) {
    vector<string> current_closure = initial_items;
    vector<string> worklist = initial_items;
    set<string> closure_set(initial_items.begin(), initial_items.end());

    while (!worklist.empty()) {
        string item = worklist.back();
        worklist.pop_back();

        size_t dot_pos = item.find('.');
        if (dot_pos != string::npos && dot_pos + 1 < item.size()) {
            char symbol_after_dot = item[dot_pos + 1];
            if (isupper(symbol_after_dot)) {
                for (const string& prod : grammar_productions) {
                    if (!prod.empty() && prod[0] == symbol_after_dot) {
                        string new_item_dotted = add_dot_after_arrow(prod);
                        if (closure_set.find(new_item_dotted) == closure_set.end()) {
                            closure_set.insert(new_item_dotted);
                            current_closure.push_back(new_item_dotted);
                            worklist.push_back(new_item_dotted);
                        }
                    }
                }
            }
        }
    }
    sort(current_closure.begin(), current_closure.end());
    return current_closure;
}

// Function: goto_set
vector<string> goto_set(const vector<string>& state_items, char symbol, const vector<string>& grammar_productions) {
    vector<string> kernel_items;
    for (const string& item : state_items) {
        size_t dot_pos = item.find('.');
        if (dot_pos != string::npos && dot_pos + 1 < item.size()) {
            if (item[dot_pos + 1] == symbol) {
                string next_item = item;
                swap(next_item[dot_pos], next_item[dot_pos + 1]);
                kernel_items.push_back(next_item);
            }
        }
    }
    return closure(kernel_items, grammar_productions);
}

// Function: generate_states_and_dfa
void generate_states_and_dfa(
    const vector<string>& grammar_productions,
    const string& augmented_start_rule,
    vector<vector<string>>& canonical_collection,
    map<int, map<char, int>>& dfa_goto
) {
    canonical_collection.clear();
    dfa_goto.clear();
    map<vector<string>, int> state_to_id;
    vector<vector<string>> items_to_process;

    string start_item = add_dot_after_arrow(augmented_start_rule);
    vector<string> initial_state_items = closure({start_item}, grammar_productions);

    canonical_collection.push_back(initial_state_items);
    state_to_id[initial_state_items] = 0;
    items_to_process.push_back(initial_state_items);
    int current_id = 0;

    while (current_id < items_to_process.size()) {
        vector<string> current_state_items = items_to_process[current_id];
        int from_state_id = current_id; // Simpler since we process in order

        set<char> possible_symbols;
        for (const string& item : current_state_items) {
            size_t dot_pos = item.find('.');
            if (dot_pos != string::npos && dot_pos + 1 < item.size()) {
                possible_symbols.insert(item[dot_pos + 1]);
            }
        }

        for (char symbol : possible_symbols) {
            vector<string> next_state_items = goto_set(current_state_items, symbol, grammar_productions);
            if (!next_state_items.empty()) {
                if (state_to_id.find(next_state_items) == state_to_id.end()) {
                    int new_state_id = canonical_collection.size();
                    state_to_id[next_state_items] = new_state_id;
                    canonical_collection.push_back(next_state_items);
                    items_to_process.push_back(next_state_items);
                    dfa_goto[from_state_id][symbol] = new_state_id;
                } else {
                    int existing_state_id = state_to_id[next_state_items];
                    dfa_goto[from_state_id][symbol] = existing_state_id;
                }
            }
        }
        current_id++;
    }
}

// --- FIRST and FOLLOW Set Computation ---

// Function: compute_first_sets (Corrected for Epsilon)
map<char, set<char>> compute_first_sets(const vector<string>& grammar) {
    map<char, set<char>> first;
    set<char> non_terminals = get_non_terminals(grammar); // Needed? Yes, to initialize map keys

    // Initialize FIRST sets for all non-terminals
    for(char nt : non_terminals) {
        first[nt] = set<char>();
    }

    bool changed;
    do {
        changed = false;
        for (const string& prod : grammar) {
            size_t arrow_pos = prod.find("->");
            if (arrow_pos == string::npos || arrow_pos == 0) continue; // Skip invalid lines
            char lhs = prod[0];
            string rhs = prod.substr(arrow_pos + 2);

            // Handle explicit epsilon production (A -> )
            if (rhs.empty()) {
                size_t before = first[lhs].size();
                first[lhs].insert(EPSILON_CHAR);
                if (first[lhs].size() > before) changed = true;
                continue; // Done with this production
            }

            bool derives_epsilon_sequence = true; // Track if the entire sequence processed so far can derive epsilon
            for (char symbol : rhs) {
                set<char> first_of_symbol;
                if (!isupper(symbol)) { // Terminal
                    first_of_symbol.insert(symbol);
                    derives_epsilon_sequence = false; // Terminal stops epsilon derivation
                } else { // Non-terminal
                    // Ensure the non-terminal exists in the map (should if grammar is valid)
                    if (first.count(symbol)) {
                         first_of_symbol = first.at(symbol);
                    } else {
                        cerr << "Warning: Non-terminal '" << symbol << "' found in RHS but not defined as LHS in grammar." << endl;
                        // Treat as unable to derive epsilon if undefined
                        derives_epsilon_sequence = false;
                    }
                }

                size_t before = first[lhs].size();
                bool symbol_has_epsilon = first_of_symbol.count(EPSILON_CHAR);

                // Add FIRST(symbol) - {epsilon} to FIRST(lhs)
                for (char f : first_of_symbol) {
                    if (f != EPSILON_CHAR) {
                        first[lhs].insert(f);
                    }
                }

                if (first[lhs].size() > before) changed = true;

                // If the current symbol cannot derive epsilon, stop processing this RHS
                if (!symbol_has_epsilon) {
                    derives_epsilon_sequence = false;
                    break;
                }
            } // End loop through RHS symbols

            // If the entire RHS sequence could derive epsilon, add epsilon to FIRST(lhs)
            if (derives_epsilon_sequence) {
                 size_t before = first[lhs].size();
                 first[lhs].insert(EPSILON_CHAR);
                 if (first[lhs].size() > before) changed = true;
            }

        } // End loop through productions
    } while (changed);

    return first;
}

// Function: compute_follow_sets
map<char, set<char>> compute_follow_sets(const vector<string>& grammar,
                                       const map<char, set<char>>& first_sets,
                                       char start_symbol) {
    map<char, set<char>> follow;
    set<char> non_terminals = get_non_terminals(grammar);

    // Initialize FOLLOW sets for all non-terminals
    for(char nt : non_terminals) {
        follow[nt] = set<char>();
    }
    follow[start_symbol].insert('$'); // Rule 1: Add $ to FOLLOW(S)

    bool changed;
    do {
        changed = false;
        for (const string& prod : grammar) {
            size_t arrow_pos = prod.find("->");
             if (arrow_pos == string::npos || arrow_pos == 0) continue;
            char lhs = prod[0]; // A in A -> alpha B beta
            string rhs = prod.substr(arrow_pos + 2); // alpha B beta

            for (size_t i = 0; i < rhs.length(); ++i) {
                char B = rhs[i];
                if (!isupper(B)) continue; // Only interested in non-terminals B

                // Look at the 'beta' part (symbols after B)
                bool beta_derives_epsilon = true;
                for (size_t j = i + 1; j < rhs.length(); ++j) {
                    char next_symbol = rhs[j];
                    set<char> first_of_next;

                    if (!isupper(next_symbol)) { // Terminal
                        first_of_next.insert(next_symbol);
                    } else { // Non-terminal
                        // Ensure the non-terminal exists in first_sets
                         if (first_sets.count(next_symbol)) {
                            first_of_next = first_sets.at(next_symbol);
                         } else {
                            cerr << "Warning: Non-terminal '" << next_symbol << "' in FOLLOW calculation missing from FIRST sets." << endl;
                         }
                    }

                    // Add FIRST(next_symbol) - {epsilon} to FOLLOW(B)
                    size_t before = follow[B].size();
                    for (char f : first_of_next) {
                        if (f != EPSILON_CHAR) {
                            follow[B].insert(f);
                        }
                    }
                    if (follow[B].size() > before) changed = true;

                    // If epsilon is not in FIRST(next_symbol), then beta cannot derive epsilon
                    if (first_of_next.find(EPSILON_CHAR) == first_of_next.end()) {
                        beta_derives_epsilon = false;
                        break; // Stop processing beta for this B
                    }
                } // End loop through beta

                // Rule 3: If beta is empty or derives epsilon (A -> alpha B beta where FIRST(beta) contains epsilon)
                // then add FOLLOW(A) to FOLLOW(B)
                if (beta_derives_epsilon) { // Includes case where beta is empty (j loop doesn't run)
                     // Ensure LHS non-terminal exists in follow map
                     if (follow.count(lhs)) {
                        const set<char>& follow_of_A = follow.at(lhs);
                        size_t before = follow[B].size();
                        follow[B].insert(follow_of_A.begin(), follow_of_A.end());
                        if (follow[B].size() > before) changed = true;
                     } else {
                          cerr << "Warning: Non-terminal '" << lhs << "' in FOLLOW calculation missing from FOLLOW sets (should not happen)." << endl;
                     }
                }
            } // End loop through RHS for B
        } // End loop through productions
    } while (changed);

    return follow;
}


// --- SLR(1) Parsing Table Construction (Corrected Conflicts) ---

void build_parsing_table(
    const vector<vector<string>>& canonical_collection,
    const map<int, map<char, int>>& dfa_goto,
    const vector<string>& original_grammar,
    const string& augmented_production_no_dot, // e.g., "X->S"
    const map<char, set<char>>& follow_sets,
    map<int, map<char, string>>& action_table,
    map<int, map<char, int>>& goto_table
) {
    action_table.clear();
    // Initialize Goto table directly from DFA transitions involving non-terminals
    goto_table.clear();
    set<char> non_terms = get_non_terminals(original_grammar);
    for (const auto& pair1 : dfa_goto) {
        int from_state = pair1.first;
        for (const auto& pair2 : pair1.second) {
            char symbol = pair2.first;
            int to_state = pair2.second;
            if (non_terms.count(symbol)) { // If it's a non-terminal transition
                goto_table[from_state][symbol] = to_state;
            }
        }
    }


    set<char> terminals = get_terminals(original_grammar); // Includes '$'
    map<string, int> prod_num; // Map original production string -> number (1-based)
    for (size_t i = 0; i < original_grammar.size(); ++i) {
        prod_num[original_grammar[i]] = i + 1;
    }

    for (int i = 0; i < canonical_collection.size(); ++i) {
        const vector<string>& state_items = canonical_collection[i];

        for (const string& item : state_items) {
            size_t dot_pos = item.find('.');
            if (dot_pos == string::npos) continue; // Should not happen

            // Case 1: Shift or Goto (Goto handled by separate table initialization)
            if (dot_pos + 1 < item.size()) {
                char symbol = item[dot_pos + 1];

                // If symbol is a terminal -> potential Shift action
                if (terminals.count(symbol)) {
                    // Check if a GOTO transition exists for this terminal symbol
                    if (dfa_goto.count(i) && dfa_goto.at(i).count(symbol)) {
                        int target_state = dfa_goto.at(i).at(symbol);
                        string shift_action = "S" + to_string(target_state);

                        // *** ADDED: Conflict Check before placing SHIFT ***
                        if (action_table.count(i) && action_table[i].count(symbol)) {
                             // Conflict exists if the current entry is different
                             if (action_table[i][symbol] != shift_action) {
                                 throw runtime_error("SLR(1) conflict (Shift/Reduce) in state " +
                                     to_string(i) + " on terminal '" + symbol +
                                     "'. Existing: " + action_table[i][symbol] + ", Attempting Shift: " + shift_action);
                             }
                             // If it's the same shift action, do nothing or overwrite (harmless)
                        } else {
                            // Place shift action only if no conflict
                            action_table[i][symbol] = shift_action;
                        }
                    }
                    // No else needed: if no goto transition, no shift action is placed
                }
                 // Non-terminal transitions are handled by the goto_table
            }
            // Case 2: Reduce or Accept
            else { // Dot is at the end: A -> alpha .
                string production_rule = item.substr(0, dot_pos); // Get rule without dot "A->alpha"

                 // Special case: Accept state X -> S .
                if (production_rule == augmented_production_no_dot) {
                     // *** ADDED: Conflict Check before placing ACCEPT ***
                     if (action_table.count(i) && action_table[i].count('$')) {
                          // Conflict exists if the current entry is different (must be Reduce)
                          if (action_table[i]['$'] != "Accept") {
                              throw runtime_error("SLR(1) conflict (Accept/Reduce) in state " +
                                  to_string(i) + " on '$'. Existing: " + action_table[i]['$'] + ", Attempting Accept.");
                          }
                           // If it's already Accept, do nothing
                     } else {
                         // Place Accept only if no conflict
                         action_table[i]['$'] = "Accept";
                     }
                }
                 // Normal Reduce case: A -> alpha . where A is not X
                else {
                    // Find the original production number (ensure it exists)
                    if (prod_num.count(production_rule)) {
                        int rule_number = prod_num[production_rule];
                        string reduce_action = "r" + to_string(rule_number);
                        char lhs_non_terminal = production_rule[0];

                        // Find FOLLOW(lhs_non_terminal)
                        if (follow_sets.count(lhs_non_terminal)) {
                             const set<char>& follow_of_lhs = follow_sets.at(lhs_non_terminal);

                             // Add reduce action for all terminals in FOLLOW(lhs)
                             for (char term_in_follow : follow_of_lhs) {
                                 // Existing Conflict Check when placing REDUCE
                                 if (action_table.count(i) && action_table[i].count(term_in_follow)) {
                                      // Conflict exists if the current entry is different
                                     if (action_table[i][term_in_follow] != reduce_action) {
                                         throw runtime_error("SLR(1) conflict (Shift/Reduce or Reduce/Reduce) in state " +
                                             to_string(i) + " on terminal '" + term_in_follow +
                                             "'. Existing: " + action_table[i][term_in_follow] + ", Attempting Reduce: " + reduce_action);
                                     }
                                     // If it's the same reduce action, do nothing
                                 } else {
                                     // Place reduce action only if no conflict
                                     action_table[i][term_in_follow] = reduce_action;
                                 }
                             }
                        } else {
                             cerr << "Warning: FOLLOW set not found for LHS non-terminal '" << lhs_non_terminal << "' during table construction." << endl;
                        }
                    } else {
                         // Should not happen if grammar and prod_num are consistent
                         cerr << "Warning: Could not find production number for reducing rule: " << production_rule << endl;
                    }
                }
            } // End Reduce/Accept case
        } // End loop through items in state
    } // End loop through states
}


// --- Parsing Engine (Unchanged from LR(0) version) ---

bool parse_input(
    const string& input_string_with_dollar,
    const map<int, map<char, string>>& action_table,
    const map<int, map<char, int>>& goto_table,
    const vector<string>& original_grammar,
    vector<vector<string>>& parse_steps
) {
    parse_steps.clear();
    vector<int> stack;
    stack.push_back(0);
    int input_ptr = 0;

    while (true) {
        int current_state = stack.back();
        char lookahead = input_string_with_dollar[input_ptr];

        string action;
        if (action_table.count(current_state) && action_table.at(current_state).count(lookahead)) {
            action = action_table.at(current_state).at(lookahead);
        } else {
            vector<string> step = {"Error: No action defined for state " + to_string(current_state) + " and lookahead '" + lookahead + "'", to_string(input_ptr), string(1, lookahead), ""};
            ostringstream stack_oss;
            stack_oss << "[";
             for(size_t j=0; j<stack.size(); ++j) stack_oss << stack[j] << (j == stack.size()-1 ? "" : ", ");
            stack_oss << "]";
            step[3] = stack_oss.str();
            parse_steps.push_back(step);
            return false;
        }

        vector<string> step = {action, to_string(input_ptr), string(1, lookahead), ""};
        ostringstream stack_oss;
        stack_oss << "[";
        for(size_t j=0; j<stack.size(); ++j) stack_oss << stack[j] << (j == stack.size()-1 ? "" : ", ");
        stack_oss << "]";
        step[3] = stack_oss.str();
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
                 throw runtime_error("Internal Error: Invalid rule number " + to_string(rule_number) + " during reduce.");
            }
            string production_rule = original_grammar[rule_number - 1];
            size_t arrow_pos = production_rule.find("->");
             if (arrow_pos == string::npos) {
                 throw runtime_error("Internal Error: Invalid production format '" + production_rule + "'");
            }
            string rhs = production_rule.substr(arrow_pos + 2);
            char lhs_non_terminal = production_rule[0];
            int pop_count = rhs.length();

             if (stack.size() < (pop_count + 1)) {
                 throw runtime_error("Internal Error: Stack underflow during reduce for rule " + production_rule);
             }
            for (int k = 0; k < pop_count; ++k) {
                stack.pop_back();
            }

            int exposed_state = stack.back();
            if (!goto_table.count(exposed_state) || !goto_table.at(exposed_state).count(lhs_non_terminal)) {
                vector<string> err_step = {"Error: Undefined GOTO state(" + to_string(exposed_state) + ", " + string(1, lhs_non_terminal) + ")", to_string(input_ptr), string(1, lookahead), ""};
                ostringstream err_stack_oss;
                err_stack_oss << "[";
                for(size_t j=0; j<stack.size(); ++j) {
                    err_stack_oss << stack[j] << (j == stack.size()-1 ? "" : ", ");
                }
                err_stack_oss << "]";
                err_step[3] = err_stack_oss.str();
                parse_steps.push_back(err_step);
                return false;
            }
            int goto_state = goto_table.at(exposed_state).at(lhs_non_terminal);
            stack.push_back(goto_state);
        } else {
             throw runtime_error("Internal Error: Unknown action type '" + action + "'");
        }
    } // end while
}


// --- Utility Functions (File I/O, Formatting) ---

string compress_name(const string &name) {
    string comp_name;
    for (char c : name) {
        if (isalnum(c)) {
            comp_name += c;
        } else {
             comp_name += '_'; // Replace non-alphanumeric with underscore
        }
    }
     if (comp_name.length() > 50) {
         comp_name = comp_name.substr(0, 50);
     }
    return comp_name.empty() ? "output" : comp_name;
}

void save_file(const string &content, int grammar_num, const string &name_suffix) {
    try {
        string directory = "parsable_strings/" + to_string(grammar_num) + "/";
        fs::create_directories(directory);
        string filename = directory + name_suffix + ".txt";
        ofstream f(filename);
        if (!f) {
            cerr << "Error: Could not open file for writing: " << filename << endl;
            return;
        }
        f << content;
        f.close();
        cout << "Output saved to: " << filename << "\n";
    } catch (const fs::filesystem_error& e) {
        cerr << "Filesystem error saving file: " << e.what() << endl;
    } catch (const exception& e) {
         cerr << "Error saving file: " << e.what() << endl;
    }
}

string format_table_to_string(const vector<vector<string>>& data, const vector<string>& header) {
     if (header.empty() && data.empty()) return "";
     size_t num_cols = header.empty() ? (data.empty() ? 0 : data[0].size()) : header.size();
     if (num_cols == 0) return "";

     vector<size_t> col_widths(num_cols, 0);

     for (size_t j = 0; j < num_cols; ++j) {
         if (j < header.size()) col_widths[j] = max(col_widths[j], header[j].length());
     }
     for (const auto& row : data) {
         for (size_t j = 0; j < num_cols; ++j) {
            if (j < row.size()) col_widths[j] = max(col_widths[j], row[j].length());
         }
     }

     ostringstream oss;
     string separator = "+";
     for (size_t width : col_widths) separator += string(width + 2, '-') + "+";
     separator += "\n";

     oss << separator;
     if (!header.empty()) {
         oss << "|";
         for (size_t j = 0; j < num_cols; ++j) {
             string cell = (j < header.size()) ? header[j] : "";
             oss << " " << left << setw(col_widths[j]) << cell << " |";
         }
         oss << "\n";
         oss << separator;
     }
     for (const auto& row : data) {
         oss << "|";
         for (size_t j = 0; j < num_cols; ++j) {
             string cell = (j < row.size()) ? row[j] : "";
              oss << " " << left << setw(col_widths[j]) << cell << " |";
         }
         oss << "\n";
     }
     oss << separator;
     return oss.str();
}


// --- Main Function ---
int main() {
    try {
        cout << "SLR(1) Parser Generator and Parser\n";
        cout << "===================================\n";
        cout << "Note: Assumes epsilon is represented by empty RHS or '" << EPSILON_CHAR << "' in grammar file.\n";


        int grammar_num;
        cout << "Enter grammar number (e.g., 1 for grammar/1.txt): ";
        cin >> grammar_num;
        cin.ignore(numeric_limits<streamsize>::max(), '\n');

        // --- Read Grammar ---
        string grammar_filename = "grammar/" + to_string(grammar_num) + ".txt";
        ifstream grammar_file(grammar_filename);
        if (!grammar_file) throw runtime_error("Cannot open grammar file: " + grammar_filename);

        vector<string> original_grammar;
        string line;
        cout << "\nReading Grammar from " << grammar_filename << ":\n";
        while (getline(grammar_file, line)) {
            line.erase(0, line.find_first_not_of(" \t\n\r\f\v"));
            line.erase(line.find_last_not_of(" \t\n\r\f\v") + 1);
            if (!line.empty()) {
                original_grammar.push_back(line);
                cout << "  " << line << endl;
            }
        }
        grammar_file.close();
        if (original_grammar.empty()) throw runtime_error("Grammar file is empty or contains no valid productions.");

        // --- Augment Grammar ---
        if (!isupper(original_grammar[0][0])) throw runtime_error("First rule's LHS must be a non-terminal (start symbol).");
        char start_symbol = original_grammar[0][0];
        string augmented_start_rule_no_dot = string("X->") + start_symbol; // Use 'X' or other unused char
        vector<string> grammar_for_states = original_grammar; // Use original for FIRST/FOLLOW/parsing
        grammar_for_states.insert(grammar_for_states.begin(), augmented_start_rule_no_dot); // Use augmented only for state gen

        cout << "\nAugmented Grammar (for state generation):\n";
        cout << "  " << augmented_start_rule_no_dot << endl;
        for(const string& prod : original_grammar) cout << "  " << prod << endl;
        cout << "---------------------------------------------------------------\n";


        // --- Generate States and DFA ---
        cout << "Generating LR(0) Item Sets (Canonical Collection)...\n";
        vector<vector<string>> canonical_collection;
        map<int, map<char, int>> dfa_goto;
        generate_states_and_dfa(grammar_for_states, augmented_start_rule_no_dot, canonical_collection, dfa_goto); // Use augmented grammar here
        cout << "Generated " << canonical_collection.size() << " states.\n";
        // Optional: Print states if needed for debugging
        // ...

        // --- Compute FIRST and FOLLOW Sets ---
        cout << "Computing FIRST sets...\n";
        map<char, set<char>> first_sets = compute_first_sets(original_grammar); // Use original grammar
         // Optional: Print FIRST sets
         // ...
        cout << "Computing FOLLOW sets...\n";
        map<char, set<char>> follow_sets = compute_follow_sets(original_grammar, first_sets, start_symbol); // Use original
         // Optional: Print FOLLOW sets
         // ...
         cout << "---------------------------------------------------------------\n";


        // --- Build Parsing Table ---
         cout << "Building SLR(1) Action and Goto Tables...\n";
        map<int, map<char, string>> action_table;
        map<int, map<char, int>> goto_table;
        build_parsing_table(canonical_collection, dfa_goto, original_grammar, // Use original grammar
                        augmented_start_rule_no_dot, follow_sets,
                        action_table, goto_table);
        cout << "Tables built successfully (or conflict detected and thrown).\n";

        // --- Display Parsing Table ---
         set<char> terminals_set = get_terminals(original_grammar); // Use original grammar
         set<char> non_terminals_set = get_non_terminals(original_grammar);

         vector<string> terminals; // Convert sets to sorted vectors for ordered columns
         for (char t : terminals_set) if (t != EPSILON_CHAR) terminals.push_back(string(1, t)); // Exclude epsilon display
         sort(terminals.begin(), terminals.end());
         if (terminals.back() != "$") { // Ensure $ is last terminal column
            auto it = find(terminals.begin(), terminals.end(), "$");
            if(it != terminals.end()) swap(*it, terminals.back()); else terminals.push_back("$");
         }


         vector<string> non_terminals;
         for(char nt : non_terminals_set) non_terminals.push_back(string(1, nt));
         sort(non_terminals.begin(), non_terminals.end());

         vector<string> header = {"State"}; // Table Header
         header.insert(header.end(), terminals.begin(), terminals.end()); // Action columns (Terminals)
         header.insert(header.end(), non_terminals.begin(), non_terminals.end()); // Goto columns (Non-Terminals)

         vector<vector<string>> table_data; // Table Body
         for (int i = 0; i < canonical_collection.size(); ++i) {
             vector<string> row;
             row.push_back(to_string(i));
             // Action Part
             for (const string& term_str : terminals) {
                  char term = term_str[0];
                 row.push_back(action_table.count(i) && action_table.at(i).count(term) ? action_table.at(i).at(term) : "");
             }
             // Goto Part
             for (const string& non_term_str : non_terminals) {
                 char non_term = non_term_str[0];
                 row.push_back(goto_table.count(i) && goto_table.at(i).count(non_term) ? to_string(goto_table.at(i).at(non_term)) : "");
             }
             table_data.push_back(row);
         }

         cout << "\nSLR(1) Parsing Table:\n";
         cout << format_table_to_string(table_data, header);
         cout << "---------------------------------------------------------------\n";


        // --- Parse Input String ---
        cout << "Enter the string to be parsed (without $): ";
        string input_string;
        getline(cin, input_string);
        input_string.erase(0, input_string.find_first_not_of(" \t\n\r\f\v"));
        input_string.erase(input_string.find_last_not_of(" \t\n\r\f\v") + 1);

        string input_with_dollar = input_string + "$";
        cout << "Parsing input: " << input_with_dollar << "\n\n";

        vector<vector<string>> parse_steps;
        bool accepted = parse_input(input_with_dollar, action_table, goto_table, original_grammar, parse_steps);

        // --- Display Parsing Steps ---
        vector<string> parse_header = {"Action/Reduce/Goto", "Input Ptr", "Lookahead", "Stack"};
        string parsing_steps_table = format_table_to_string(parse_steps, parse_header);
        cout << "Parsing Steps:\n";
        cout << parsing_steps_table;
        cout << "---------------------------------------------------------------\n";

        // --- Report Result & Save ---
         string file_base_name = compress_name(input_string);
        if (accepted) {
            cout << "Result: SUCCESS! String \"" << input_string << "\" is accepted by the grammar.\n";
            save_file(parsing_steps_table, grammar_num, file_base_name + "_accepted");
        } else {
            cout << "Result: FAILURE! String \"" << input_string << "\" is rejected by the grammar.\n";
            save_file(parsing_steps_table, grammar_num, file_base_name + "_rejected");
        }

    } catch (const fs::filesystem_error& e) {
        cerr << "\nFilesystem Error: " << e.what() << endl;
        cerr << "Ensure 'grammar' directory exists and has read permissions." << endl;
        cerr << "Ensure permissions allow creating 'parsable_strings' directory and files." << endl;
        return 1;
    } catch (const runtime_error& e) {
        cerr << "\nRuntime Error: " << e.what() << endl;
         if (string(e.what()).find("SLR(1) conflict") != string::npos) {
             cerr << "The provided grammar is not SLR(1) due to the reported conflict." << endl;
         }
        return 1;
    } catch (const exception& e) {
        cerr << "\nAn unexpected standard exception occurred: " << e.what() << endl;
        return 1;
    } catch (...) {
        cerr << "\nAn unknown error occurred." << endl;
        return 1;
    }

    return 0;
}