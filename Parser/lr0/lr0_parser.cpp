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

using namespace std;
namespace fs = std::filesystem;

// --- Helper Functions ---

// Replaces "->" with "->."
string add_dot_after_arrow(const string &production) {
    size_t arrow_pos = production.find("->");
    if (arrow_pos == string::npos) {
        return production; // Should not happen with valid grammar
    }
    string modified_prod = production;
    modified_prod.insert(arrow_pos + 2, ".");
    return modified_prod;
}

// Sorts items within a state for canonical representation
vector<string> get_sorted_state(const vector<string>& state) {
    vector<string> sorted_state = state;
    sort(sorted_state.begin(), sorted_state.end());
    return sorted_state;
}

// --- Core LR(0) Functions ---

// Function: closure
// Computes the closure of a set of LR(0) items.
vector<string> closure(const vector<string>& initial_items, const vector<string>& grammar_productions) {
    vector<string> current_closure = initial_items;
    vector<string> worklist = initial_items; // Items to process

    set<string> closure_set(initial_items.begin(), initial_items.end()); // For quick existence checks

    while (!worklist.empty()) {
        string item = worklist.back();
        worklist.pop_back();

        size_t dot_pos = item.find('.');
        // Check if dot exists and is not at the very end
        if (dot_pos != string::npos && dot_pos + 1 < item.size()) {
            char symbol_after_dot = item[dot_pos + 1];

            // If it's a non-terminal, add its productions
            if (isupper(symbol_after_dot)) {
                for (const string& prod : grammar_productions) {
                    // Check if production starts with the symbol after the dot
                    if (!prod.empty() && prod[0] == symbol_after_dot) {
                        string new_item_base = prod;
                        string new_item_dotted = add_dot_after_arrow(new_item_base);

                        // Add to closure and worklist only if it's new
                        if (closure_set.find(new_item_dotted) == closure_set.end()) {
                            closure_set.insert(new_item_dotted);
                            current_closure.push_back(new_item_dotted);
                            worklist.push_back(new_item_dotted);
                        }
                    }
                }
            }
        }
        // No 'else' needed here - if dot is at end or missing, no expansion occurs from this item
    }
    // Sort the final closure for canonical representation before returning
    sort(current_closure.begin(), current_closure.end());
    return current_closure;
}

// Function: goto_set
// Computes the GOTO set for a given state (set of items) and a grammar symbol.
vector<string> goto_set(const vector<string>& state_items, char symbol, const vector<string>& grammar_productions) {
    vector<string> kernel_items;
    for (const string& item : state_items) {
        size_t dot_pos = item.find('.');
        if (dot_pos != string::npos && dot_pos + 1 < item.size()) {
            if (item[dot_pos + 1] == symbol) {
                // Move the dot one position to the right
                string next_item = item;
                swap(next_item[dot_pos], next_item[dot_pos + 1]);
                kernel_items.push_back(next_item);
            }
        }
    }
    // Return the closure of the kernel items
    return closure(kernel_items, grammar_productions);
}

// Function: get_terminals
set<char> get_terminals(const vector<string>& gram) {
    set<char> terms;
    for (const string& p : gram) {
        size_t arrowPos = p.find("->");
        if (arrowPos == string::npos) continue;
        string right = p.substr(arrowPos + 2);
        for (char t : right) {
            if (!isupper(t) && t != '.' && t != '\0') { // Exclude dot and null
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
     // Add start symbol explicitly if needed, assuming it's the LHS of the first rule
    if (!gram.empty()) {
         size_t arrowPosFirst = gram[0].find("->");
         if(arrowPosFirst != string::npos && arrowPosFirst > 0) {
              non_terms.insert(gram[0][0]);
         }
    }
    for (const string& p : gram) {
        // Add LHS non-terminal
         size_t arrowPos = p.find("->");
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


// Function: generate_states_and_dfa
// Generates all LR(0) states and the DFA transitions.
void generate_states_and_dfa(
    const vector<string>& grammar_productions,      // Original grammar rules
    const string& augmented_start_rule,            // E.g., "X->S"
    vector<vector<string>>& canonical_collection,   // Output: List of states (each state is a vector<string> of items)
    map<int, map<char, int>>& dfa_goto             // Output: DFA transitions map<from_state, map<symbol, to_state>>
) {
    canonical_collection.clear();
    dfa_goto.clear();

    map<vector<string>, int> state_to_id; // Map canonical (sorted) state to its ID
    vector<vector<string>> items_to_process; // Worklist of states

    // 1. Initial State (Closure of augmented start rule)
    string start_item = add_dot_after_arrow(augmented_start_rule);
    vector<string> initial_state_items = closure({start_item}, grammar_productions);
    // initial_state_items is already sorted by closure function

    canonical_collection.push_back(initial_state_items);
    state_to_id[initial_state_items] = 0;
    items_to_process.push_back(initial_state_items);

    int current_id = 0;

    // 2. Process states from the worklist
    while (current_id < items_to_process.size()) {
        vector<string> current_state_items = items_to_process[current_id];
        int from_state_id = state_to_id[current_state_items]; // Should be == current_id

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
            vector<string> next_state_items = goto_set(current_state_items, symbol, grammar_productions);
            // next_state_items is already sorted by closure function

            if (!next_state_items.empty()) {
                // Check if this state (sorted) already exists
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


// Function: build_parsing_table
// Builds the LR(0) Action and Goto tables. Throws if not LR(0).
void build_parsing_table(
    const vector<vector<string>>& canonical_collection, // All states
    const map<int, map<char, int>>& dfa_goto,          // DFA transitions
    const vector<string>& original_grammar,             // Without augmented rule
    const string& augmented_production,                // E.g., "X->S" with dot removed
    map<int, map<char, string>>& action_table,          // Output: Action table
    map<int, map<char, int>>& goto_table                // Output: Goto table
) {
    action_table.clear();
    goto_table = dfa_goto; // Goto table is directly from non-terminal transitions in DFA

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

            // Case 1: Shift or Accept
            if (dot_pos + 1 < item.size()) {
                char symbol = item[dot_pos + 1];
                if (terminals.count(symbol)) { // It's a terminal -> Shift
                    if (dfa_goto.count(i) && dfa_goto.at(i).count(symbol)) {
                        int target_state = dfa_goto.at(i).at(symbol);
                        string shift_action = "S" + to_string(target_state);

                        // Check for Shift/Reduce conflict
                        if (action_table.count(i) && action_table[i].count(symbol) && action_table[i][symbol][0] == 'r') {
                             throw runtime_error("Grammar is not LR(0): Shift/Reduce conflict in state " + to_string(i) + " on symbol '" + symbol + "'");
                        }
                        // Check for Shift/Shift conflict (shouldn't happen with deterministic DFA)
                        if (action_table.count(i) && action_table[i].count(symbol) && action_table[i][symbol][0] == 'S' && action_table[i][symbol] != shift_action) {
                             throw runtime_error("Grammar is not LR(0): Shift/Shift conflict detected (internal error likely) in state " + to_string(i) + " on symbol '" + symbol + "'");
                        }
                         action_table[i][symbol] = shift_action;
                    } else {
                         // This indicates an issue in dfa generation if symbol follows dot
                         // cerr << "Warning: No DFA transition for terminal '" << symbol << "' from state " << i << endl;
                    }
                }
                // Non-terminal transitions are handled by the goto_table initialization
            }
            // Case 2: Reduce
            else { // Dot is at the end: A -> alpha .
                string production_rule = item.substr(0, dot_pos); // Get rule without dot "A->alpha"

                 // Special case: Accept state X -> S .
                if (production_rule == augmented_production) {
                     if (action_table.count(i) && action_table[i].count('$') && action_table[i]['$'] != "Accept") {
                         // This could be S/R on $ if another reduce action exists
                         if (action_table[i]['$'][0] == 'r') {
                              throw runtime_error("Grammar is not LR(0): Reduce/Reduce conflict (Accept vs Reduce) in state " + to_string(i) + " on '$'");
                         } else { // S/Accept conflict (shouldn't happen with $)
                            throw runtime_error("Grammar is not LR(0): Shift/Accept conflict in state " + to_string(i) + " on '$'");
                         }
                     }
                    action_table[i]['$'] = "Accept";
                } else {
                    // Find the original production number
                    if (prod_num.count(production_rule)) {
                        int rule_number = prod_num[production_rule];
                        string reduce_action = "r" + to_string(rule_number);

                        // Add reduce action for all terminals (including $)
                        for (char term : terminals) {
                            // Check for Shift/Reduce conflict
                            if (action_table.count(i) && action_table[i].count(term) && action_table[i][term][0] == 'S') {
                                throw runtime_error("Grammar is not LR(0): Shift/Reduce conflict in state " + to_string(i) + " on symbol '" + term + "' for reduction " + production_rule);
                            }
                            // Check for Reduce/Reduce conflict
                            if (action_table.count(i) && action_table[i].count(term) && action_table[i][term][0] == 'r' && action_table[i][term] != reduce_action) {
                                throw runtime_error("Grammar is not LR(0): Reduce/Reduce conflict in state " + to_string(i) + " on symbol '" + term + "'");
                            }
                             if (!action_table.count(i) || !action_table[i].count(term)) { // Avoid overwriting Accept on $
                                action_table[i][term] = reduce_action;
                             } else if (term == '$' && action_table[i][term] != "Accept") { // Allow overwriting non-accept actions on $
                                action_table[i][term] = reduce_action;
                             }
                        }
                    } else {
                        // This indicates an issue with production mapping
                         cerr << "Warning: Could not find production number for reducing rule: " << production_rule << endl;
                    }
                }
            }
        }
    }
}


// --- Parsing ---

// Function: parse_input
// Parses the input string using the LR(0) tables.
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
        int current_state = stack.back();
        char lookahead = input_string_with_dollar[input_ptr];

        string action;
        if (action_table.count(current_state) && action_table.at(current_state).count(lookahead)) {
            action = action_table.at(current_state).at(lookahead);
        } else {
            // Error: No action defined
            vector<string> step = {"Error: No action", to_string(input_ptr), string(1, lookahead), ""};
            ostringstream stack_oss;
            stack_oss << "[";
             for(size_t j=0; j<stack.size(); ++j) stack_oss << stack[j] << (j == stack.size()-1 ? "" : ", ");
            stack_oss << "]";
            step[3] = stack_oss.str();
            parse_steps.push_back(step);
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
            // stack.push_back(lookahead); // Standard LR pushes symbol THEN state conceptually
            stack.push_back(target_state); // Push state
            input_ptr++;
        } else if (action[0] == 'r') { // Reduce
            int rule_number = stoi(action.substr(1));
            // Find the production rule A -> alpha using rule_number (1-based index)
            if (rule_number < 1 || rule_number > original_grammar.size()) {
                 throw runtime_error("Internal Error: Invalid rule number " + to_string(rule_number) + " during reduce.");
            }
            string production_rule = original_grammar[rule_number - 1]; // 0-based index

            size_t arrow_pos = production_rule.find("->");
            if (arrow_pos == string::npos) {
                 throw runtime_error("Internal Error: Invalid production format '" + production_rule + "'");
            }
            string rhs = production_rule.substr(arrow_pos + 2);
            char lhs_non_terminal = production_rule[0];

            // Pop 2 * |alpha| items (symbol + state) -> Correction: Pop |alpha| states
            int pop_count = rhs.length(); // Length of the RHS determines pops
             if (stack.size() < (pop_count + 1)) { // Need at least pop_count states + 1 below them
                 throw runtime_error("Internal Error: Stack underflow during reduce for rule " + production_rule);
             }
            for (int k = 0; k < pop_count; ++k) {
                stack.pop_back();
                 // stack.pop_back(); // Pop symbol if it were pushed
            }

            // Find the state exposed after popping
            int exposed_state = stack.back();

            // Look up GOTO state
            if (!goto_table.count(exposed_state) || !goto_table.at(exposed_state).count(lhs_non_terminal)) {
                // If GOTO is undefined, it's an error in the table or grammar isn't LR(0)
                vector<string> err_step = {"Error: Undefined GOTO state(" + to_string(exposed_state) + ", " + string(1, lhs_non_terminal) + ")", to_string(input_ptr), string(1, lookahead), ""};
                ostringstream err_stack_oss;
                err_stack_oss << "[";
                // *** FIX HERE: Use stack, not err ***
                for(size_t j=0; j<stack.size(); ++j) {
                    err_stack_oss << stack[j] << (j == stack.size()-1 ? "" : ", ");
                }
                err_stack_oss << "]";
                err_step[3] = err_stack_oss.str();
                parse_steps.push_back(err_step);
                return false;
            }
            int goto_state = goto_table.at(exposed_state).at(lhs_non_terminal);

            // Push the GOTO state
            // stack.push_back(lhs_non_terminal); // Symbol (conceptual)
            stack.push_back(goto_state); // State

        } else {
            // Should not happen if action was found but isn't S, r, or Accept
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
        }
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
    } catch (const fs::filesystem_error& e) {
        cerr << "Filesystem error: " << e.what() << endl;
    } catch (const exception& e) {
         cerr << "Error saving file: " << e.what() << endl;
    }
}

// Function: to_string_table (Simplified ASCII table)
string format_table_to_string(const vector<vector<string>>& data, const vector<string>& header) {
     if (header.empty() && data.empty()) return "";
     size_t num_cols = header.empty() ? (data.empty() ? 0 : data[0].size()) : header.size();
     if (num_cols == 0) return "";

     vector<size_t> col_widths(num_cols, 0);

     // Calculate widths based on header
     for (size_t j = 0; j < num_cols; ++j) {
         if (j < header.size()) {
            col_widths[j] = max(col_widths[j], header[j].length());
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
        cout << "LR(0) Parser Generator and Parser\n";
        cout << "===================================\n";

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
            // Basic trim (remove leading/trailing whitespace)
            line.erase(0, line.find_first_not_of(" \t\n\r\f\v"));
            line.erase(line.find_last_not_of(" \t\n\r\f\v") + 1);
            if (!line.empty()) {
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
        string start_symbol_str(1, original_grammar[0][0]); // Assuming S is LHS of first rule
        string augmented_start_rule_no_dot = "X->" + start_symbol_str; // Use a distinct start symbol 'X'
        vector<string> augmented_grammar = original_grammar;
        augmented_grammar.insert(augmented_grammar.begin(), augmented_start_rule_no_dot); // Keep augmented rule *without dot* here for reference

        cout << "\nAugmented Grammar (for internal use):\n";
        cout << "  " << augmented_start_rule_no_dot << endl;
        for(const string& prod : original_grammar) cout << "  " << prod << endl;
        cout << "---------------------------------------------------------------\n";


        // --- Generate States and DFA ---
        cout << "Generating LR(0) States...\n";
        vector<vector<string>> canonical_collection;
        map<int, map<char, int>> dfa_goto;
        generate_states_and_dfa(original_grammar, augmented_start_rule_no_dot, canonical_collection, dfa_goto);

        cout << "Generated " << canonical_collection.size() << " states.\n";
        cout << "\nCanonical Collection of LR(0) Item Sets:\n";
        for (size_t i = 0; i < canonical_collection.size(); ++i) {
            cout << "State " << i << ":\n";
            for (const string& item : canonical_collection[i]) {
                cout << "  " << item << "\n";
            }
        }
         cout << "---------------------------------------------------------------\n";


        // --- Build Parsing Table ---
         cout << "Building Action and Goto Tables...\n";
        map<int, map<char, string>> action_table;
        map<int, map<char, int>> goto_table; // Note: goto_table is filled by build_parsing_table now
        build_parsing_table(canonical_collection, dfa_goto, original_grammar, augmented_start_rule_no_dot, action_table, goto_table);

        // --- Display Parsing Table ---
        set<char> terminals_set = get_terminals(original_grammar);
        set<char> non_terminals_set = get_non_terminals(original_grammar);

        // *** FIX HERE: Iterate to convert char to string ***
        vector<string> terminals;
        for (char t : terminals_set) {
            terminals.push_back(string(1, t));
        }
        vector<string> non_terminals;
        for(char nt : non_terminals_set) {
            non_terminals.push_back(string(1, nt));
        }
        sort(terminals.begin(), terminals.end()); // Sort after conversion
        sort(non_terminals.begin(), non_terminals.end());


        vector<string> header = {"State"};
        header.insert(header.end(), terminals.begin(), terminals.end());
        header.insert(header.end(), non_terminals.begin(), non_terminals.end());

         vector<vector<string>> table_data;
         for (int i = 0; i < canonical_collection.size(); ++i) {
             vector<string> row;
             row.push_back(to_string(i));
             // Action Part
             for (const string& term_str : terminals) {
                  char term = term_str[0];
                 if (action_table.count(i) && action_table.at(i).count(term)) {
                     row.push_back(action_table.at(i).at(term));
                 } else {
                     row.push_back(""); // Empty cell
                 }
             }
             // Goto Part
             for (const string& non_term_str : non_terminals) {
                 char non_term = non_term_str[0];
                  if (goto_table.count(i) && goto_table.at(i).count(non_term)) {
                      row.push_back(to_string(goto_table.at(i).at(non_term)));
                  } else {
                      row.push_back(""); // Empty cell
                  }
             }
             table_data.push_back(row);
         }

         cout << "\nLR(0) Parsing Table:\n";
         cout << format_table_to_string(table_data, header);
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
        vector<string> parse_header = {"Action/Reduce/Goto", "Input Ptr", "Lookahead", "Stack"};
        string parsing_steps_table = format_table_to_string(parse_steps, parse_header);
        cout << "Parsing Steps:\n";
        cout << parsing_steps_table;
        cout << "---------------------------------------------------------------\n";


        // --- Report Result ---
        if (accepted) {
            cout << "Result: SUCCESS! String \"" << input_string << "\" is accepted by the grammar.\n";
            string compressed_name = compress_name(input_string);
            string filename_suffix = compressed_name.empty() ? "accepted_string" : compressed_name;
            save_file(parsing_steps_table, grammar_num, filename_suffix);
            cout << "Parsing table saved to parsable_strings/" << grammar_num << "/" << filename_suffix << ".txt\n";
        } else {
            cout << "Result: FAILURE! String \"" << input_string << "\" is rejected by the grammar.\n";
            // You might want to save the steps even for rejected strings for debugging
             string compressed_name = compress_name(input_string);
             string filename_suffix = (compressed_name.empty() ? "rejected_string" : compressed_name) + "_rejected";
             save_file(parsing_steps_table, grammar_num, filename_suffix);
             cout << "Parsing steps saved to parsable_strings/" << grammar_num << "/" << filename_suffix << ".txt\n";
        }

    } catch (const fs::filesystem_error& e) {
        cerr << "\nFilesystem Error: " << e.what() << endl;
        cerr << "Please ensure the 'grammar' directory exists and contains the required file." << endl;
        cerr << "Also check permissions for creating the 'parsable_strings' directory." << endl;
        return 1;
    } catch (const runtime_error& e) {
        cerr << "\nRuntime Error: " << e.what() << endl;
         if (string(e.what()).find("Grammar is not LR(0)") != string::npos) {
             cerr << "The provided grammar cannot be parsed using a simple LR(0) parser due to conflicts." << endl;
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