#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>
#include <map>
#include <set>
#include <algorithm>
#include <filesystem>
#include <stdexcept>
#include <iterator>
#include <exception>
#include <iomanip>
#include <limits>

using namespace std;
namespace fs = filesystem;


string add_dot_after_arrow(const string &production) {
    size_t arrow_pos = production.find("->");
    if (arrow_pos == string::npos) {
        // Handle cases where '->' might be missing, although invalid grammar
        // Maybe return "." + production or throw error? For LR(0), assume valid format.
        return production;
    }
    string modified_prod = production;
    modified_prod.insert(arrow_pos + 2, ".");
    return modified_prod;
}


vector<string> get_sorted_state(const vector<string>& state) {
    vector<string> sorted_state = state;
    sort(sorted_state.begin(), sorted_state.end());
    return sorted_state;
}


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
                    if (!prod.empty() && prod.length() > 2 && prod.find("->") == 0) continue; // Skip if format is "->..."
                    if (!prod.empty() && prod[0] == symbol_after_dot) {
                        string new_item_base = prod;
                        string new_item_dotted = add_dot_after_arrow(new_item_base);

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
    // Sort the final closure for canonical representation
    sort(current_closure.begin(), current_closure.end());
    return current_closure;
}


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
    // Return the closure of the kernel items
    return closure(kernel_items, grammar_productions);
}


set<char> get_terminals(const vector<string>& gram) {
    set<char> terms;
    for (const string& p : gram) {
        size_t arrowPos = p.find("->");
        if (arrowPos == string::npos) continue;
        string right = p.substr(arrowPos + 2);
        for (char t : right) {
            // islower or !isupper usually covers terminals, excludes Non-Terminals
            if (!isupper(t) && t != '.' && t != '\0') {
                terms.insert(t);
            }
        }
    }
    terms.insert('$'); // Add end-of-input marker
    return terms;
}


set<char> get_non_terminals(const vector<string>& gram) {
    set<char> non_terms;
    // Ensure start symbol is included
    if (!gram.empty()) {
         size_t arrowPosFirst = gram[0].find("->");
         if(arrowPosFirst != string::npos && arrowPosFirst > 0 && isupper(gram[0][0])) {
              non_terms.insert(gram[0][0]);
         }
    }
    // Iterate through all productions
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


void generate_states_and_dfa(
    const vector<string>& grammar_productions_with_augmented, // Pass grammar including augmented rule
    const string& augmented_start_rule, // Only needed for initial closure
    vector<vector<string>>& canonical_collection,
    map<int, map<char, int>>& dfa_goto
) {
    canonical_collection.clear();
    dfa_goto.clear();

    // Map canonical (sorted) state (vector<string>) to its ID
    map<vector<string>, int> state_to_id;
    vector<vector<string>> items_to_process; // Worklist of states

    // 1. Initial State (Closure of augmented start rule item [X -> .S])
    string start_item = add_dot_after_arrow(augmented_start_rule);
    // Closure needs the full grammar including the augmented rule to expand .S correctly
    vector<string> initial_state_items = closure({start_item}, grammar_productions_with_augmented);
    // initial_state_items is already sorted by closure function

    canonical_collection.push_back(initial_state_items);
    state_to_id[initial_state_items] = 0;
    items_to_process.push_back(initial_state_items);

    int current_id = 0;

    // 2. Process states from the worklist
    while (current_id < items_to_process.size()) {
        vector<string> current_state_items = items_to_process[current_id];
        int from_state_id = current_id; // Simpler since processed in order

        // Find all possible symbols following a dot in the current state
        set<char> possible_symbols;
        for (const string& item : current_state_items) {
            size_t dot_pos = item.find('.');
            if (dot_pos != string::npos && dot_pos + 1 < item.size()) {
                possible_symbols.insert(item[dot_pos + 1]);
            }
        }

        // Calculate GOTO for each symbol
        for (char symbol : possible_symbols) {
            // goto_set also needs the full grammar for its internal closure call
            vector<string> next_state_items = goto_set(current_state_items, symbol, grammar_productions_with_augmented);
            // next_state_items is already sorted by closure function

            if (!next_state_items.empty()) {
                // Check if this state (sorted vector<string>) already exists
                if (state_to_id.find(next_state_items) == state_to_id.end()) {
                    // New state found
                    int new_state_id = canonical_collection.size();
                    state_to_id[next_state_items] = new_state_id;
                    canonical_collection.push_back(next_state_items);
                    items_to_process.push_back(next_state_items); // Add to worklist
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


// Function: build_parsing_table (LR(0) specific)
void build_parsing_table(
    const vector<vector<string>>& canonical_collection, // LR(0) states
    const map<int, map<char, int>>& dfa_goto,           // DFA transitions
    const vector<string>& original_grammar,             // Original grammar rules (for reduce)
    const string& augmented_production,                 // E.g., "X->S" (rule string only)
    map<int, map<char, string>>& action_table,          // Output: Action table
    map<int, map<char, int>>& goto_table_out            // Output: Goto table
) {
    action_table.clear();
    goto_table_out.clear(); // Initialize the output GOTO table

    // 1. Populate GOTO table from DFA transitions on non-terminals
    set<char> non_terms = get_non_terminals(original_grammar);
     for (const auto& pair1 : dfa_goto) {
        int from_state = pair1.first;
        for (const auto& pair2 : pair1.second) {
            char symbol = pair2.first;
            int to_state = pair2.second;
            if (non_terms.count(symbol)) {
                goto_table_out[from_state][symbol] = to_state;
            }
        }
    }

    // 2. Populate ACTION table
    set<char> terminals = get_terminals(original_grammar); // Includes '$'
    map<string, int> prod_num;
    for (size_t i = 0; i < original_grammar.size(); ++i) {
        prod_num[original_grammar[i]] = i + 1; // 1-based numbering for reduce actions
    }

    // Extract LHS and RHS of augmented rule for comparison
    char augmented_start_lhs = augmented_production[0];
    string augmented_rhs = augmented_production.substr(augmented_production.find("->") + 2);


    for (int i = 0; i < canonical_collection.size(); ++i) {
        const vector<string>& state_items = canonical_collection[i];
        bool reduce_action_exists = false; // Track if a reduce action exists in this state
        string existing_reduce_action = ""; // Store the reduce action string if one exists

        for (const string& item : state_items) {
            size_t dot_pos = item.find('.');
            if (dot_pos == string::npos) continue; // Should not happen in valid items

            // Case 1: Shift Action ([A -> α . t β], where t is a terminal)
            if (dot_pos + 1 < item.size()) {
                char symbol = item[dot_pos + 1];
                if (terminals.count(symbol) && symbol != '$') { // Shift only on actual terminals
                    if (dfa_goto.count(i) && dfa_goto.at(i).count(symbol)) {
                        int target_state = dfa_goto.at(i).at(symbol);
                        string shift_action = "S" + to_string(target_state);

                        // Check for Shift/Reduce conflict: if a reduce already exists for this state
                        if (reduce_action_exists) {
                             throw runtime_error("Grammar is not LR(0): Shift/Reduce conflict in state " + to_string(i) + " on symbol '" + string(1,symbol) + "' (shift vs existing reduce " + existing_reduce_action + ")");
                        }
                        // Check for Shift/Shift conflict (shouldn't happen with deterministic DFA)
                        if (action_table.count(i) && action_table[i].count(symbol) && action_table[i][symbol] != shift_action) {
                             throw runtime_error("Grammar is not LR(0): Shift/Shift conflict detected (internal error likely) in state " + to_string(i) + " on symbol '" + string(1,symbol) + "'");
                        }
                         action_table[i][symbol] = shift_action;
                    }
                     // If DFA doesn't have transition, table entry remains empty
                }
            }
            // Case 2: Reduce or Accept Action ([A -> α .])
            else { // Dot is at the end
                 string production_rule = item.substr(0, dot_pos); // Rule before dot, e.g., "A->alpha"

                 // Construct the comparison string for the augmented rule (no dot)
                 string augmented_compare_rule = string(1,augmented_start_lhs) + "->" + augmented_rhs;


                // Accept Action? (Augmented production's final item)
                if (production_rule == augmented_compare_rule) {
                     // Check for conflict with existing Reduce action on '$'
                     if (reduce_action_exists && existing_reduce_action != "Accept") {
                         throw runtime_error("Grammar is not LR(0): Reduce/Reduce conflict (Accept vs Reduce "+existing_reduce_action+") in state " + to_string(i) + " on '$'");
                     }
                      // Check conflict with existing Accept (should be same)
                     if (action_table.count(i) && action_table[i].count('$') && action_table[i]['$'] != "Accept") {
                          throw runtime_error("Grammar is not LR(0): Conflict (Accept vs " + action_table[i]['$'] + ") in state " + to_string(i) + " on '$'");
                     }
                     action_table[i]['$'] = "Accept";
                     reduce_action_exists = true; // Treat Accept as a kind of reduce for conflict detection
                     existing_reduce_action = "Accept";
                }
                // Reduce Action? (Normal production's final item)
                else {
                    // Find the original production number
                    if (prod_num.count(production_rule)) {
                        int rule_number = prod_num[production_rule];
                        string reduce_action = "r" + to_string(rule_number);

                         // Check for Reduce/Reduce conflict
                         if (reduce_action_exists && existing_reduce_action != reduce_action) {
                             throw runtime_error("Grammar is not LR(0): Reduce/Reduce conflict in state " + to_string(i) + " (Existing: "+existing_reduce_action+", New: "+reduce_action+")");
                         }

                        // Add reduce action for ALL terminals (including $)
                        for (char term : terminals) {
                            // Check for Shift/Reduce conflict: If a shift exists for this terminal
                             if (action_table.count(i) && action_table[i].count(term) && action_table[i][term][0] == 'S') {
                                throw runtime_error("Grammar is not LR(0): Shift/Reduce conflict in state " + to_string(i) + " on symbol '" + string(1,term) + "' (shift " + action_table[i][term] +" vs reduce "+reduce_action+")");
                             }
                             // Add/overwrite reduce action (check for existing Accept on '$')
                             if (!action_table.count(i) || !action_table[i].count(term) || (term == '$' && action_table[i][term] != "Accept")) {
                                 action_table[i][term] = reduce_action;
                             } else if (term != '$') { // Allow overwriting previous reduce if not '$' and not Accept
                                 action_table[i][term] = reduce_action;
                             }
                        }
                        reduce_action_exists = true; // Mark that a reduce action exists
                        existing_reduce_action = reduce_action; // Store which reduce action it is
                    } else {
                         // This indicates an issue matching the reduced rule back to the original grammar
                         cerr << "Warning: Could not find production number for reducing rule: '" << production_rule << "' in state " << i << endl;
                    }
                }
            }
        } // End loop over items in state
    } // End loop over states
}


bool parse_input(
    const string& input_string_with_dollar,
    const map<int, map<char, string>>& action_table,
    const map<int, map<char, int>>& goto_table,
    const vector<string>& original_grammar,
    vector<vector<string>>& parse_steps
) {
    parse_steps.clear();
    vector<int> state_stack;
    vector<char> symbol_stack; // For displaying the stack content
    state_stack.push_back(0); // Initial state

    int input_ptr = 0;

    while (true) {
        if (state_stack.empty()) { // Should not happen in correct operation
             parse_steps.push_back({"Error: Stack empty", input_string_with_dollar.substr(input_ptr), "FAIL"});
             return false;
        }
        int current_state = state_stack.back();
        char lookahead = input_string_with_dollar[input_ptr];

        string action;
        if (action_table.count(current_state) && action_table.at(current_state).count(lookahead)) {
            action = action_table.at(current_state).at(lookahead);
        } else {
             string error_msg = "Error: No action defined for state " + to_string(current_state) + " and lookahead '" + lookahead + "'";

             ostringstream stack_oss; // Build stack string for error display
             stack_oss << "[";
             if (!state_stack.empty()) {
                 stack_oss << state_stack[0];
                 for (size_t i = 0; i < symbol_stack.size(); ++i) {
                     if (i + 1 < state_stack.size()) {
                        stack_oss << " " << symbol_stack[i] << " " << state_stack[i+1];
                     } else {
                         stack_oss << " " << symbol_stack[i] << " ?STATE?";
                     }
                 }
             }
             stack_oss << "]";
             string stack_str = stack_oss.str();
             string input_buffer = input_string_with_dollar.substr(input_ptr);
             parse_steps.push_back({stack_str, input_buffer, error_msg});
             return false;
        }

        // Build stack string for normal step display
        ostringstream stack_oss;
         stack_oss << "[";
         if (!state_stack.empty()) {
             stack_oss << state_stack[0];
             for (size_t i = 0; i < symbol_stack.size(); ++i) {
                  if (i + 1 < state_stack.size()) {
                      stack_oss << " " << symbol_stack[i] << " " << state_stack[i+1];
                  } else {
                       stack_oss << " " << symbol_stack[i] << " ?STATE?";
                  }
             }
         }
         stack_oss << "]";
         string stack_str = stack_oss.str();
         string input_buffer = input_string_with_dollar.substr(input_ptr);
         parse_steps.push_back({stack_str, input_buffer, action});


        if (action == "Accept") {
            return true;
        } else if (action[0] == 'S') {
            int target_state = stoi(action.substr(1));
            symbol_stack.push_back(lookahead); // Push the terminal symbol
            state_stack.push_back(target_state); // Push the target state
            input_ptr++;
        } else if (action[0] == 'r') {
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

            int pop_count = rhs.length(); // Pop symbols corresponding to RHS length

             if (state_stack.size() < (pop_count + 1)) {
                 throw runtime_error("Internal Error: State stack underflow during reduce for rule " + production_rule);
             }
              if (symbol_stack.size() < pop_count) {
                 throw runtime_error("Internal Error: Symbol stack underflow during reduce for rule " + production_rule);
             }

            // Pop pop_count symbols and pop_count states
            for (int k = 0; k < pop_count; ++k) {
                if (!state_stack.empty()) state_stack.pop_back();
                if (!symbol_stack.empty()) symbol_stack.pop_back();
            }


            if (state_stack.empty()) { // Should not happen if checks above are correct
                throw runtime_error("Internal Error: State stack empty after pop during reduce for rule " + production_rule);
            }
            int exposed_state = state_stack.back();


            if (!goto_table.count(exposed_state) || !goto_table.at(exposed_state).count(lhs_non_terminal)) {
                 string error_msg = "Error: Undefined GOTO state(" + to_string(exposed_state) + ", " + string(1, lhs_non_terminal) + ")";
                 ostringstream err_stack_oss; // Build stack string for error display
                 err_stack_oss << "[";
                 if (!state_stack.empty()) {
                     err_stack_oss << state_stack[0];
                     for (size_t i = 0; i < symbol_stack.size(); ++i) {
                         if (i + 1 < state_stack.size()) {
                            err_stack_oss << " " << symbol_stack[i] << " " << state_stack[i+1];
                         } else {
                             err_stack_oss << " " << symbol_stack[i] << " ?STATE?";
                         }
                     }
                 }
                 err_stack_oss << "]";
                 string err_stack_str = err_stack_oss.str();
                 string err_input_buffer = input_string_with_dollar.substr(input_ptr);
                 parse_steps.push_back({err_stack_str, err_input_buffer, error_msg});
                return false;
            }
            int goto_state = goto_table.at(exposed_state).at(lhs_non_terminal);

            symbol_stack.push_back(lhs_non_terminal); // Push the non-terminal symbol
            state_stack.push_back(goto_state); // Push the GOTO state

        } else {
             throw runtime_error("Internal Error: Unknown action type '" + action + "'");
        }
    }
}



string compress_name(const string &name) {
    string comp_name;
    for (char c : name) {
        if (isalnum(c)) {
            comp_name += c;
        } else if (comp_name.length() > 0 && comp_name.back() != '_'){ // Avoid multiple underscores
            comp_name += '_';
        }
    }
    if (!comp_name.empty() && comp_name.back() == '_') {
        comp_name.pop_back(); // Remove trailing underscore
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

        string filename = directory + name_suffix + ".txt"; // Suffix already includes parser type
        ofstream f(filename);
        if (!f) {
            cerr << "Error: Could not open file for writing: " << filename << endl;
            return;
        }
        f << content;
        f.close();
        cout << "Output saved to: " << filename << "\n"; // Confirmation message
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
         if (j < header.size()) {
            col_widths[j] = max(col_widths[j], header[j].length());
         }
     }

     for (const auto& row : data) {
         for (size_t j = 0; j < num_cols; ++j) {
            if (j < row.size()) {
                col_widths[j] = max(col_widths[j], row[j].length());
            }
         }
     }

    // Adjust min width for better table look
     for (size_t j = 0; j < num_cols; ++j) {
        if (!header.empty()) { // Check header exists before accessing
            if (header[j] == "Stack") col_widths[j] = max(col_widths[j], (size_t)15);
            else if (header[j] == "Input Buffer") col_widths[j] = max(col_widths[j], (size_t)15);
            else if (header[j] == "Action") col_widths[j] = max(col_widths[j], (size_t)10);
            else col_widths[j] = max(col_widths[j], (size_t)5); // Min width for other columns
        } else {
            col_widths[j] = max(col_widths[j], (size_t)5); // Default min width if no header
        }
     }


     ostringstream oss;
     string separator = "+";
     for (size_t width : col_widths) {
         separator += string(width + 2, '-') + "+";
     }
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


int main() {
    try {
        cout << "LR(0) Parser Generator and Parser\n";
        cout << "===================================\n";

        int grammar_num;
        cout << "Enter grammar number: ";
        cin >> grammar_num;
        cin.ignore(numeric_limits<streamsize>::max(), '\n');


        string grammar_filename = "grammar/" + to_string(grammar_num) + ".txt";
        ifstream grammar_file(grammar_filename);
        if (!grammar_file) {
             throw runtime_error("Cannot open grammar file: " + grammar_filename);
        }

        vector<string> original_grammar;
        string line;
        cout << "\nReading Grammar from " << grammar_filename << ":\n";
        while (getline(grammar_file, line)) {
            line.erase(0, line.find_first_not_of(" \t\n\r\f\v"));
            line.erase(line.find_last_not_of(" \t\n\r\f\v") + 1);
            if (!line.empty() && line.find("->") != string::npos) {
                original_grammar.push_back(line);
                cout << "  " << line << endl;
            } else if (!line.empty() && line.rfind("//", 0) != 0){ // Ignore comments
                cout << "  Skipping invalid line (no '->'): " << line << endl;
            }
        }
        grammar_file.close();

        if (original_grammar.empty()) {
             throw runtime_error("Grammar file is empty or contains no valid productions.");
        }
        if (!isupper(original_grammar[0][0])) {
             throw runtime_error("First rule's LHS must be an uppercase non-terminal (Start Symbol).");
        }


        string start_symbol_str(1, original_grammar[0][0]);
        char augmented_start_char = 'X';
         set<char> all_symbols;
         for(char c : get_terminals(original_grammar)) all_symbols.insert(c);
         for(char c : get_non_terminals(original_grammar)) all_symbols.insert(c);
         while(all_symbols.count(augmented_start_char)) {
            if(augmented_start_char == 'Z') throw runtime_error("Could not find unused non-terminal for augmented grammar.");
            augmented_start_char++;
         }

        string augmented_start_rule_no_dot = string(1, augmented_start_char) + "->" + start_symbol_str;
        vector<string> grammar_for_states = original_grammar; // Create a copy
        grammar_for_states.insert(grammar_for_states.begin(), augmented_start_rule_no_dot); // Add augmented rule for state gen

        cout << "\nAugmented Grammar (for state generation):\n";
        cout << "  " << augmented_start_rule_no_dot << endl;
        //for(const string& prod : original_grammar) cout << "  " << prod << endl; // No need to print original again
        cout << "---------------------------------------------------------------\n";


        cout << "Generating LR(0) Item Sets (Canonical Collection)...\n";
        vector<vector<string>> canonical_collection;
        map<int, map<char, int>> dfa_goto;
        generate_states_and_dfa(grammar_for_states, augmented_start_rule_no_dot, canonical_collection, dfa_goto); // Pass grammar WITH augmented rule

        cout << "Generated " << canonical_collection.size() << " states.\n";

        cout << "\nCanonical LR(0) Item Sets:\n";
        for (size_t i = 0; i < canonical_collection.size(); ++i) {
            cout << "I_" << i << ":\n";
            for (const string& item : canonical_collection[i]) {
                cout << "  " << item << "\n";
            }
             cout << endl;
        }
        cout << "---------------------------------------------------------------\n";


        cout << "Building LR(0) Action and Goto Tables...\n";
        map<int, map<char, string>> action_table;
        map<int, map<char, int>> goto_table;
        build_parsing_table(canonical_collection, dfa_goto, original_grammar, augmented_start_rule_no_dot, action_table, goto_table);
         cout << "Tables built successfully (or conflict detected and thrown).\n";

        set<char> terminals_set = get_terminals(original_grammar);
        set<char> non_terminals_set = get_non_terminals(original_grammar);


        vector<string> terminals;
        for (char t : terminals_set) terminals.push_back(string(1, t));
        sort(terminals.begin(), terminals.end());
        auto dollar_it = find(terminals.begin(), terminals.end(), "$");
         if(dollar_it != terminals.end()) {
            rotate(dollar_it, dollar_it + 1, terminals.end());
         }


        vector<string> non_terminals;
        for(char nt : non_terminals_set) non_terminals.push_back(string(1, nt));
        sort(non_terminals.begin(), non_terminals.end());


        vector<string> header = {"State"};
        header.insert(header.end(), terminals.begin(), terminals.end());
        header.insert(header.end(), non_terminals.begin(), non_terminals.end());

         vector<vector<string>> table_data;
         for (int i = 0; i < canonical_collection.size(); ++i) {
             vector<string> row;
             row.push_back(to_string(i));

             for (const string& term_str : terminals) {
                  char term = term_str[0];
                 row.push_back(action_table.count(i) && action_table.at(i).count(term) ? action_table.at(i).at(term) : "");
             }

             for (const string& non_term_str : non_terminals) {
                 char non_term = non_term_str[0];
                 row.push_back(goto_table.count(i) && goto_table.at(i).count(non_term) ? to_string(goto_table.at(i).at(non_term)) : "");
             }
             table_data.push_back(row);
         }

         cout << "\nLR(0) Parsing Table:\n";
         string lr0_table_string = format_table_to_string(table_data, header); // Store table string
         cout << lr0_table_string;
         cout << "---------------------------------------------------------------\n";


        cout << "Enter the string to be parsed (without $): ";
        string input_string;
        getline(cin, input_string);

        input_string.erase(0, input_string.find_first_not_of(" \t\n\r\f\v"));
        input_string.erase(input_string.find_last_not_of(" \t\n\r\f\v") + 1);

        string input_with_dollar = input_string + "$";
        cout << "Parsing input: " << input_with_dollar << "\n\n";

        vector<vector<string>> parse_steps;
        bool accepted = parse_input(input_with_dollar, action_table, goto_table, original_grammar, parse_steps);

        vector<string> parse_header = {"Stack", "Input Buffer", "Action"};
        string parsing_steps_table = format_table_to_string(parse_steps, parse_header);
        cout << "Parsing Steps:\n";
        cout << parsing_steps_table;
        cout << "---------------------------------------------------------------\n";


        string file_base_name = compress_name(input_string);
        string result_string;
        string file_suffix;

        if (accepted) {
            result_string = "Result: SUCCESS! String \"" + input_string + "\" is accepted by the LR(0) grammar.\n";
            file_suffix = file_base_name + "_lr0"; // Suffix for accepted file
        } else {
            result_string = "Result: FAILURE! String \"" + input_string + "\" is rejected by the LR(0) grammar.\n";
             if(!parse_steps.empty() && parse_steps.back().back().find("Error:") != string::npos) {
                 result_string += "Reason: " + parse_steps.back().back() + "\n";
             }
            file_suffix = file_base_name + "_lr0_rejected"; // Suffix for rejected file
        }
        cout << result_string; // Print result to console

        // Construct content for saving
        string file_content_to_save;
        file_content_to_save += "Grammar File: " + grammar_filename + "\n";
        file_content_to_save += "Input String: " + input_string + "\n\n";
        file_content_to_save += "LR(0) Parsing Table:\n";
        file_content_to_save += lr0_table_string + "\n"; // Add the LR(0) table
        file_content_to_save += "Parsing Steps:\n";
        file_content_to_save += parsing_steps_table + "\n"; // Add the parsing steps
        file_content_to_save += result_string; // Add the final result string

        save_file(file_content_to_save, grammar_num, file_suffix); // Save the combined content


    } catch (const fs::filesystem_error& e) {
        cerr << "\nFilesystem Error: " << e.what() << endl;
         cerr << "Please ensure the 'grammar' directory exists and contains the required file." << endl;
         cerr << "Also check permissions for creating the 'parsable_strings' directory." << endl;
        return 1;
    } catch (const runtime_error& e) {
         cerr << "\nRuntime Error: " << e.what() << endl;
         if (string(e.what()).find("Grammar is not LR(0)") != string::npos) {
              cerr << "The provided grammar cannot be parsed using an LR(0) parser due to conflicts." << endl;
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