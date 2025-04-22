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

const char EPSILON_CHAR = '#';


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
            if (!isupper(t) && t != EPSILON_CHAR && t != '\0') {
                terms.insert(t);
            }
        }
    }
    terms.insert('$');
    return terms;
}

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
    return non_terms;
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
                    if (!prod.empty() && prod.length() > 2 && prod.substr(0, 2) == "->" ) continue; // Skip invalid format
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
    sort(initial_state_items.begin(), initial_state_items.end()); // Ensure initial state is sorted

    canonical_collection.push_back(initial_state_items);
    state_to_id[initial_state_items] = 0;
    items_to_process.push_back(initial_state_items);
    int current_id = 0;

    while (current_id < items_to_process.size()) {
        vector<string> current_state_items = items_to_process[current_id];
        int from_state_id = current_id;

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
                sort(next_state_items.begin(), next_state_items.end()); // Sort for consistent map key
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


map<char, set<char>> compute_first_sets(const vector<string>& grammar) {
    map<char, set<char>> first;
    set<char> non_terminals = get_non_terminals(grammar);

    for(char nt : non_terminals) {
        first[nt] = set<char>();
    }

    bool changed;
    do {
        changed = false;
        for (const string& prod : grammar) {
            size_t arrow_pos = prod.find("->");
            if (arrow_pos == string::npos || arrow_pos == 0) continue;
            char lhs = prod[0];
            string rhs = prod.substr(arrow_pos + 2);


            if (rhs.empty()) { // Treat empty RHS as epsilon
                 size_t before = first[lhs].size();
                 first[lhs].insert(EPSILON_CHAR);
                 if (first[lhs].size() > before) changed = true;
                 continue;
            }


            bool derives_epsilon_sequence = true;
            for (char symbol : rhs) {
                 // Note: No check for EPSILON_CHAR here, assuming it's only for empty prod

                set<char> first_of_symbol;
                if (!isupper(symbol)) {
                    first_of_symbol.insert(symbol);
                    derives_epsilon_sequence = false;
                } else {
                    if (first.count(symbol)) {
                         first_of_symbol = first.at(symbol);
                    } else {
                        cerr << "Warning: Non-terminal '" << symbol << "' found in RHS but not defined as LHS in grammar." << endl;
                        derives_epsilon_sequence = false; // Cannot determine if it derives epsilon
                    }
                }

                size_t before = first[lhs].size();
                bool symbol_has_epsilon = first_of_symbol.count(EPSILON_CHAR);


                for (char f : first_of_symbol) {
                    if (f != EPSILON_CHAR) {
                        first[lhs].insert(f);
                    }
                }

                if (first[lhs].size() > before) changed = true;


                if (!symbol_has_epsilon) {
                    derives_epsilon_sequence = false;
                    break;
                }
            }

            if (derives_epsilon_sequence) {
                 size_t before = first[lhs].size();
                 first[lhs].insert(EPSILON_CHAR);
                 if (first[lhs].size() > before) changed = true;
            }

        }
    } while (changed);

    return first;
}


map<char, set<char>> compute_follow_sets(const vector<string>& grammar,
                                       const map<char, set<char>>& first_sets,
                                       char start_symbol) {
    map<char, set<char>> follow;
    set<char> non_terminals = get_non_terminals(grammar);

    for(char nt : non_terminals) {
        follow[nt] = set<char>();
    }
    follow[start_symbol].insert('$');

    bool changed;
    do {
        changed = false;
        for (const string& prod : grammar) {
            size_t arrow_pos = prod.find("->");
             if (arrow_pos == string::npos || arrow_pos == 0) continue;
            char lhs = prod[0];
            string rhs = prod.substr(arrow_pos + 2);

            for (size_t i = 0; i < rhs.length(); ++i) {
                char B = rhs[i];
                if (!isupper(B)) continue;

                bool beta_derives_epsilon = true;
                for (size_t j = i + 1; j < rhs.length(); ++j) {
                    char next_symbol = rhs[j];
                     // if (next_symbol == EPSILON_CHAR) continue; // Not needed if # only for empty

                    set<char> first_of_next;

                    if (!isupper(next_symbol)) {
                        first_of_next.insert(next_symbol);
                    } else {
                         if (first_sets.count(next_symbol)) {
                            first_of_next = first_sets.at(next_symbol);
                         } else {
                            cerr << "Warning: Non-terminal '" << next_symbol << "' in FOLLOW calculation missing from FIRST sets." << endl;
                         }
                    }

                    size_t before = follow[B].size();
                    for (char f : first_of_next) {
                        if (f != EPSILON_CHAR) {
                            follow[B].insert(f);
                        }
                    }
                    if (follow[B].size() > before) changed = true;

                    if (first_of_next.find(EPSILON_CHAR) == first_of_next.end()) {
                        beta_derives_epsilon = false;
                        break;
                    }
                }

                if (beta_derives_epsilon) {
                     if (follow.count(lhs)) {
                        const set<char>& follow_of_A = follow.at(lhs);
                        size_t before = follow[B].size();
                        follow[B].insert(follow_of_A.begin(), follow_of_A.end());
                        if (follow[B].size() > before) changed = true;
                     } else {
                          cerr << "Warning: Non-terminal '" << lhs << "' in FOLLOW calculation missing from FOLLOW sets (should not happen)." << endl;
                     }
                }
            }
        }
    } while (changed);

    return follow;
}


void build_parsing_table(
    const vector<vector<string>>& canonical_collection,
    const map<int, map<char, int>>& dfa_goto,
    const vector<string>& original_grammar,
    const string& augmented_production_no_dot,
    const map<char, set<char>>& follow_sets,
    map<int, map<char, string>>& action_table,
    map<int, map<char, int>>& goto_table
) {
    action_table.clear();
    goto_table.clear();
    set<char> non_terms = get_non_terminals(original_grammar);
    for (const auto& pair1 : dfa_goto) {
        int from_state = pair1.first;
        for (const auto& pair2 : pair1.second) {
            char symbol = pair2.first;
            int to_state = pair2.second;
            if (non_terms.count(symbol)) {
                goto_table[from_state][symbol] = to_state;
            }
        }
    }


    set<char> terminals = get_terminals(original_grammar);
    map<string, int> prod_num;
    for (size_t i = 0; i < original_grammar.size(); ++i) {
        prod_num[original_grammar[i]] = i + 1;
    }

    for (int i = 0; i < canonical_collection.size(); ++i) {
        const vector<string>& state_items = canonical_collection[i];

        for (const string& item : state_items) {
            size_t dot_pos = item.find('.');
            if (dot_pos == string::npos) continue;


            if (dot_pos + 1 < item.size()) {
                char symbol = item[dot_pos + 1];

                if (terminals.count(symbol)) {
                    if (dfa_goto.count(i) && dfa_goto.at(i).count(symbol)) {
                        int target_state = dfa_goto.at(i).at(symbol);
                        string shift_action = "S" + to_string(target_state);


                        if (action_table.count(i) && action_table[i].count(symbol)) {
                             if (action_table[i][symbol] != shift_action) {
                                 throw runtime_error("SLR(1) conflict (Shift/Reduce) in state " +
                                     to_string(i) + " on terminal '" + string(1,symbol) + // Use string(1,symbol) here
                                     "'. Existing: " + action_table[i][symbol] + ", Attempting Shift: " + shift_action);
                             }

                        } else {

                            action_table[i][symbol] = shift_action;
                        }
                    }

                }

            }

            else { // Dot at the end
                string production_rule_with_arrow = item.substr(0, dot_pos); // e.g., "X->S." becomes "X->S"
                string production_rule_no_dot = production_rule_with_arrow; // For comparison


                if (production_rule_no_dot == augmented_production_no_dot) {
                     if (action_table.count(i) && action_table[i].count('$')) {
                          if (action_table[i]['$'] != "Accept") {
                              throw runtime_error("SLR(1) conflict (Accept vs " + action_table[i]['$'] + ") in state " + // Added conflicting action
                                  to_string(i) + " on '$'.");
                          }

                     } else {
                         action_table[i]['$'] = "Accept";
                     }
                }

                else {
                     // Need to find the original grammar rule string (without dot)
                     string original_rule_lookup = production_rule_no_dot;


                    if (prod_num.count(original_rule_lookup)) {
                        int rule_number = prod_num[original_rule_lookup];
                        string reduce_action = "r" + to_string(rule_number);
                         char lhs_non_terminal = original_rule_lookup[0];


                        if (follow_sets.count(lhs_non_terminal)) {
                             const set<char>& follow_of_lhs = follow_sets.at(lhs_non_terminal);

                             for (char term_in_follow : follow_of_lhs) {
                                 if (action_table.count(i) && action_table[i].count(term_in_follow)) {
                                     if (action_table[i][term_in_follow] != reduce_action) {
                                         throw runtime_error("SLR(1) conflict (Shift/Reduce or Reduce/Reduce) in state " +
                                             to_string(i) + " on terminal '" + string(1, term_in_follow) + // Use string(1,term_in_follow)
                                             "'. Existing: " + action_table[i][term_in_follow] + ", Attempting Reduce: " + reduce_action);
                                     }
                                 } else {
                                     action_table[i][term_in_follow] = reduce_action;
                                 }
                             }
                        } else {
                             cerr << "Warning: FOLLOW set not found for LHS non-terminal '" << lhs_non_terminal << "' during table construction." << endl;
                        }
                    } else {

                         cerr << "Warning: Could not find production number for reducing rule: " << original_rule_lookup << endl;
                    }
                }
            }
        }
    }
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
    vector<char> symbol_stack; // For display purposes
    state_stack.push_back(0);
    int input_ptr = 0;

    while (true) {
        int current_state = state_stack.back();
        char lookahead = input_string_with_dollar[input_ptr];

        string action;
        if (action_table.count(current_state) && action_table.at(current_state).count(lookahead)) {
            action = action_table.at(current_state).at(lookahead);
        } else {
             string error_msg = "Error: No action defined for state " + to_string(current_state) + " and lookahead '" + lookahead + "'";
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
             parse_steps.push_back({stack_str, input_buffer, error_msg});
             return false;
        }


        ostringstream stack_oss;
        stack_oss << "[";
         if (!state_stack.empty()) {
             stack_oss << state_stack[0];
             for (size_t i = 0; i < symbol_stack.size(); ++i) {
                 if (i + 1 < state_stack.size()) {
                    stack_oss << " " << symbol_stack[i] << " " << state_stack[i+1];
                 } else {
                     stack_oss << " " << symbol_stack[i] << " ?STATE?"; // Should not happen if stacks are synced
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
            symbol_stack.push_back(lookahead); // Push terminal
            state_stack.push_back(target_state);
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
             int pop_count = 0;
             if (!rhs.empty()) { // Check if RHS is actually empty (handled epsilon earlier)
                pop_count = rhs.length();
             }


             if (state_stack.size() < (pop_count + 1)) {
                  // This check might be slightly off if symbol_stack logic is primary
                 throw runtime_error("Internal Error: State stack underflow during reduce for rule " + production_rule);
             }
             if (symbol_stack.size() < pop_count) {
                 throw runtime_error("Internal Error: Symbol stack underflow during reduce for rule " + production_rule);
             }


            for (int k = 0; k < pop_count; ++k) {
                 if (!state_stack.empty()) state_stack.pop_back();
                 if (!symbol_stack.empty()) symbol_stack.pop_back();
            }

             if(state_stack.empty()) {
                  throw runtime_error("Internal Error: State stack empty after pop during reduce for rule " + production_rule);
             }
            int exposed_state = state_stack.back();


            if (!goto_table.count(exposed_state) || !goto_table.at(exposed_state).count(lhs_non_terminal)) {
                 string error_msg = "Error: Undefined GOTO state(" + to_string(exposed_state) + ", " + string(1, lhs_non_terminal) + ")";
                 ostringstream err_stack_oss;
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
            symbol_stack.push_back(lhs_non_terminal); // Push non-terminal
            state_stack.push_back(goto_state);
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
        } else if (comp_name.length() > 0 && comp_name.back() != '_') { // Prevent multiple underscores
             comp_name += '_';
        }
    }
    if (!comp_name.empty() && comp_name.back() == '_') {
        comp_name.pop_back(); // Remove trailing underscore
    }
     if (comp_name.length() > 50) { // Limit length
         comp_name = comp_name.substr(0, 50);
     }
    return comp_name.empty() ? "output" : comp_name;
}

void save_file(const string &content, int grammar_num, const string &name_suffix) {
    try {
        string directory = "parsable_strings/" + to_string(grammar_num) + "/";
        fs::create_directories(directory);
        string filename = directory + name_suffix + ".txt"; // Suffix already contains parser type
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
            if (j < row.size()) {
                col_widths[j] = max(col_widths[j], row[j].length());
            }
         }
     }

     // Adjust min width for better table look
     for (size_t j = 0; j < num_cols; ++j) {
        if (header[j] == "Stack") col_widths[j] = max(col_widths[j], (size_t)15);
        else if (header[j] == "Input Buffer") col_widths[j] = max(col_widths[j], (size_t)15);
        else if (header[j] == "Action") col_widths[j] = max(col_widths[j], (size_t)10);
        else col_widths[j] = max(col_widths[j], (size_t)5); // Min width for other columns
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


int main() {
    try {
        cout << "SLR(1) Parser Generator and Parser\n";
        cout << "===================================\n";
        cout << "Note: Assumes epsilon is represented by empty RHS in grammar file.\n";


        int grammar_num;
        cout << "Enter grammar number: ";
        cin >> grammar_num;
        cin.ignore(numeric_limits<streamsize>::max(), '\n');


        string grammar_filename = "grammar/" + to_string(grammar_num) + ".txt";
        ifstream grammar_file(grammar_filename);
        if (!grammar_file) throw runtime_error("Cannot open grammar file: " + grammar_filename);

        vector<string> original_grammar;
        string line;
        cout << "\nReading Grammar from " << grammar_filename << ":\n";
        while (getline(grammar_file, line)) {
            line.erase(0, line.find_first_not_of(" \t\n\r\f\v"));
            line.erase(line.find_last_not_of(" \t\n\r\f\v") + 1);
             if (!line.empty() && line.find("->") != string::npos) {
                 size_t arrow_pos = line.find("->");
                 string rhs = line.substr(arrow_pos + 2);
                 // Trim RHS to check for emptiness representing epsilon
                 rhs.erase(0, rhs.find_first_not_of(" \t"));
                 rhs.erase(rhs.find_last_not_of(" \t") + 1);
                 if (rhs.empty()) {
                    // Store empty RHS rule as is, it represents epsilon
                    line = line.substr(0, arrow_pos + 2);
                 }
                original_grammar.push_back(line);
                cout << "  " << line << (rhs.empty() ? " (Epsilon Rule)" : "") << endl;
            } else if (!line.empty() && line.rfind("//", 0) != 0) { // Allow comments
                cout << "  Skipping non-production line: " << line << endl;
            }
        }
        grammar_file.close();
        if (original_grammar.empty()) throw runtime_error("Grammar file is empty or contains no valid productions.");


        if (!isupper(original_grammar[0][0])) throw runtime_error("First rule's LHS must be a non-terminal (start symbol).");
        char start_symbol = original_grammar[0][0];
        char augmented_start_char = 'X'; // Default 'X'
         set<char> all_symbols;
         for(char c : get_terminals(original_grammar)) all_symbols.insert(c);
         for(char c : get_non_terminals(original_grammar)) all_symbols.insert(c);
         while(all_symbols.count(augmented_start_char)) { // Find an unused uppercase char
            if(augmented_start_char == 'Z') throw runtime_error("Could not find unused non-terminal for augmented grammar.");
            augmented_start_char++;
         }


        string augmented_start_rule_no_dot = string(1, augmented_start_char) + "->" + start_symbol;
        vector<string> grammar_for_states = original_grammar;
        grammar_for_states.insert(grammar_for_states.begin(), augmented_start_rule_no_dot);

        cout << "\nAugmented Grammar (for state generation):\n";
        cout << "  " << augmented_start_rule_no_dot << endl;
        //for(const string& prod : original_grammar) cout << "  " << prod << endl; // Redundant
        cout << "---------------------------------------------------------------\n";



        cout << "Generating LR(0) Item Sets (Canonical Collection)...\n";
        vector<vector<string>> canonical_collection;
        map<int, map<char, int>> dfa_goto;
        generate_states_and_dfa(grammar_for_states, augmented_start_rule_no_dot, canonical_collection, dfa_goto);
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



        cout << "Computing FIRST sets...\n";
        map<char, set<char>> first_sets = compute_first_sets(original_grammar);

        cout << "Computing FOLLOW sets...\n";
        map<char, set<char>> follow_sets = compute_follow_sets(original_grammar, first_sets, start_symbol);

         cout << "---------------------------------------------------------------\n";



         cout << "Building SLR(1) Action and Goto Tables...\n";
        map<int, map<char, string>> action_table;
        map<int, map<char, int>> goto_table;
        build_parsing_table(canonical_collection, dfa_goto, original_grammar,
                        augmented_start_rule_no_dot, follow_sets,
                        action_table, goto_table);
        cout << "Tables built successfully (or conflict detected and thrown).\n";


         set<char> terminals_set = get_terminals(original_grammar);
         set<char> non_terminals_set = get_non_terminals(original_grammar);


         vector<string> terminals;
         for (char t : terminals_set) if (t != EPSILON_CHAR && t != '\0') terminals.push_back(string(1, t));
         sort(terminals.begin(), terminals.end());
         auto dollar_it = find(terminals.begin(), terminals.end(), "$");
         if(dollar_it != terminals.end()) {
            rotate(dollar_it, dollar_it + 1, terminals.end());
         } else if (terminals_set.count('$')) { // Ensure $ is present if needed
            terminals.push_back("$");
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

         cout << "\nSLR(1) Parsing Table:\n";
         string slr_table_string = format_table_to_string(table_data, header); // Store table string
         cout << slr_table_string;
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
            result_string = "Result: SUCCESS! String \"" + input_string + "\" is accepted by the SLR(1) grammar.\n";
            file_suffix = file_base_name + "_slr1"; // Suffix for accepted file
        } else {
            result_string = "Result: FAILURE! String \"" + input_string + "\" is rejected by the SLR(1) grammar.\n";
             if(!parse_steps.empty() && parse_steps.back().back().find("Error:") != string::npos) {
                 result_string += "Reason: " + parse_steps.back().back() + "\n";
             }
            file_suffix = file_base_name + "_slr1_rejected"; // Suffix for rejected file
        }
        cout << result_string; // Print result to console

        // Construct content for saving
        string file_content_to_save;
        file_content_to_save += "Grammar File: " + grammar_filename + "\n";
        file_content_to_save += "Input String: " + input_string + "\n\n";
        file_content_to_save += "SLR(1) Parsing Table:\n";
        file_content_to_save += slr_table_string + "\n"; // Add the SLR table
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
         if (string(e.what()).find("SLR(1) conflict") != string::npos) {
             cerr << "The provided grammar is not SLR(1)." << endl;
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