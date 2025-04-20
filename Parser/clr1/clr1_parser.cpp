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
namespace fs = filesystem;

using Clr1Item = pair<string, char>;

const char EPSILON = '@';

string add_dot_after_arrow(const string &production) {
    size_t arrow_pos = production.find("->");
    if (arrow_pos == string::npos) {
        return "." + production;
    }
    string modified_prod = production;
    modified_prod.insert(arrow_pos + 2, ".");
    return modified_prod;
}

vector<Clr1Item> get_sorted_state(const vector<Clr1Item>& state) {
    vector<Clr1Item> sorted_state = state;
    sort(sorted_state.begin(), sorted_state.end());
    return sorted_state;
}

set<char> get_terminals(const vector<string>& gram) {
    set<char> terms;
    for (const string& p : gram) {
        size_t arrowPos = p.find("->");
        if (arrowPos == string::npos) continue;
        string right = p.substr(arrowPos + 2);
        for (char t : right) {
            if (!isupper(t) && t != '.' && t != '\0' && t != EPSILON ) {
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
     if (!gram.empty()) {
         size_t arrowPosFirst = gram[0].find("->");
         if(arrowPosFirst != string::npos && arrowPosFirst > 0 && isupper(gram[0][0])) {
              non_terms.insert(gram[0][0]);
         } else if (!gram.empty() && isupper(gram[0][0])) {
         }
     }
    return non_terms;
}

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
         else {
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

    for (char t : terminals) {
        first_sets[t].insert(t);
    }
    first_sets[EPSILON].insert(EPSILON);
    first_sets['$'].insert('$');

    for (char nt : non_terminals) {
        first_sets[nt] = set<char>();
    }

    bool changed = true;
    while (changed) {
        changed = false;
        for (const string& prod : grammar_productions) {
            size_t arrow_pos = prod.find("->");
            if (arrow_pos == string::npos || arrow_pos == 0) continue;

            char lhs = prod[0];
            if (!non_terminals.count(lhs)) continue;

            string rhs = prod.substr(arrow_pos + 2);
            if (rhs.empty()) rhs = string(1, EPSILON);


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
                sequence_after_B += lookahead;

                set<char> lookaheads_for_new_items = first_of_sequence(sequence_after_B, first_sets, non_terminals);

                for (const string& prod : grammar_productions) {
                    if (!prod.empty() && prod[0] == symbol_after_dot) {
                        string new_item_base = prod;
                        string new_item_dotted = add_dot_after_arrow(new_item_base);

                        for (char b : lookaheads_for_new_items) {
                            if (b == EPSILON) continue;

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
    return get_sorted_state(current_closure);
}

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
    return closure(kernel_items, grammar_productions, first_sets, non_terminals);
}


void generate_states_and_dfa(
    const vector<string>& grammar_productions,
    const string& augmented_start_rule,
    const map<char, set<char>>& first_sets,
    const set<char>& non_terminals,
    vector<vector<Clr1Item>>& canonical_collection,
    map<int, map<char, int>>& dfa_goto
) {
    canonical_collection.clear();
    dfa_goto.clear();

    map<vector<Clr1Item>, int> state_to_id;
    vector<vector<Clr1Item>> states_to_process;

    string start_item_rule = add_dot_after_arrow(augmented_start_rule);
    Clr1Item initial_clr_item = {start_item_rule, '$'};

    vector<Clr1Item> initial_state_items = closure({initial_clr_item}, grammar_productions, first_sets, non_terminals);

    canonical_collection.push_back(initial_state_items);
    state_to_id[initial_state_items] = 0;
    states_to_process.push_back(initial_state_items);

    int current_id = 0;

    while (current_id < states_to_process.size()) {
        vector<Clr1Item> current_state_items = states_to_process[current_id];
        int from_state_id = state_to_id[current_state_items];

        set<char> possible_symbols;
        for (const Clr1Item& item : current_state_items) {
            const string& rule = item.first;
            size_t dot_pos = rule.find('.');
            if (dot_pos != string::npos && dot_pos + 1 < rule.size()) {
                possible_symbols.insert(rule[dot_pos + 1]);
            }
        }

        for (char symbol : possible_symbols) {
             if (symbol == EPSILON) continue;

            vector<Clr1Item> next_state_items = goto_set(current_state_items, symbol, grammar_productions, first_sets, non_terminals);

            if (!next_state_items.empty()) {
                if (state_to_id.find(next_state_items) == state_to_id.end()) {
                    int new_state_id = canonical_collection.size();
                    state_to_id[next_state_items] = new_state_id;
                    canonical_collection.push_back(next_state_items);
                    states_to_process.push_back(next_state_items);
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

void build_parsing_table(
    const vector<vector<Clr1Item>>& canonical_collection,
    const map<int, map<char, int>>& dfa_goto,
    const vector<string>& original_grammar,
    const string& augmented_production_no_dot,
    const set<char>& terminals,
    const set<char>& non_terminals,
    map<int, map<char, string>>& action_table,
    map<int, map<char, int>>& goto_table
) {
    action_table.clear();
    goto_table.clear();

    for(const auto& [from_state, transitions] : dfa_goto) {
        for (const auto& [symbol, to_state] : transitions) {
            if (non_terminals.count(symbol)) {
                goto_table[from_state][symbol] = to_state;
            }
        }
    }

    map<string, int> prod_num;
    for (size_t i = 0; i < original_grammar.size(); ++i) {
        prod_num[original_grammar[i]] = i + 1;
    }

    for (int i = 0; i < canonical_collection.size(); ++i) {
        const vector<Clr1Item>& state_items = canonical_collection[i];

        for (const Clr1Item& item : state_items) {
            string rule = item.first;
            char lookahead = item.second;
            size_t dot_pos = rule.find('.');
            if (dot_pos == string::npos) continue;

            if (dot_pos + 1 < rule.size()) {
                char symbol_after_dot = rule[dot_pos + 1];
                if (terminals.count(symbol_after_dot)) {
                    if (dfa_goto.count(i) && dfa_goto.at(i).count(symbol_after_dot)) {
                        int target_state = dfa_goto.at(i).at(symbol_after_dot);
                        string shift_action = "S" + to_string(target_state);

                        if (action_table.count(i) && action_table[i].count(symbol_after_dot)) {
                            const string& existing_action = action_table[i][symbol_after_dot];
                            if (existing_action != shift_action) {
                                throw runtime_error("Grammar is not CLR(1): Conflict (likely Shift/Reduce) in state " + to_string(i) + " on terminal '" + symbol_after_dot + "'. Existing: " + existing_action + ", New: " + shift_action);
                            }
                        } else {
                            action_table[i][symbol_after_dot] = shift_action;
                        }
                    } else {
                         cerr << "Warning: No DFA transition found for terminal '" << symbol_after_dot << "' from state " << i << ", although item " << rule << " suggests one." << endl;
                    }
                }
            }
            else {
                string production_rule = rule.substr(0, dot_pos);

                if (production_rule == augmented_production_no_dot) {
                     if (lookahead == '$') {
                        string accept_action = "Accept";
                        if (action_table.count(i) && action_table[i].count('$')) {
                             const string& existing_action = action_table[i]['$'];
                             if (existing_action != accept_action) {
                                 throw runtime_error("Grammar is not CLR(1): Conflict (Accept vs " + existing_action + ") in state " + to_string(i) + " on '$'.");
                             }
                        } else {
                             action_table[i]['$'] = accept_action;
                        }
                    }
                }
                else {
                    if (prod_num.count(production_rule)) {
                        int rule_number = prod_num[production_rule];
                        string reduce_action = "r" + to_string(rule_number);

                         if (action_table.count(i) && action_table[i].count(lookahead)) {
                             const string& existing_action = action_table[i][lookahead];
                             if (existing_action != reduce_action) {
                                 throw runtime_error(std::string("Grammar is not CLR(1): Conflict (") +
                                    (existing_action[0] == 'S' ? "Shift/Reduce" : "Reduce/Reduce") +
                                    ") in state " + std::to_string(i) + " on lookahead '" + lookahead +
                                    "'. Existing: " + existing_action + ", New: " + reduce_action +
                                    " (from rule " + production_rule + ")");
                             }
                         } else {
                             action_table[i][lookahead] = reduce_action;
                         }
                    } else {
                        cerr << "Warning: Could not find production number for reducing rule: " << production_rule << endl;
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
    vector<string> stack; // Stores states and symbols as strings
    stack.push_back(to_string(0)); // Initial state is always 0

    int input_ptr = 0;

    while (true) {
        if (stack.empty()) {
             string remaining_input = input_string_with_dollar.substr(input_ptr);
             vector<string> step = {"[]", remaining_input, "Error: Stack unexpectedly empty"};
             parse_steps.push_back(step);
             return false;
        }
        int current_state = stoi(stack.back()); // Current state is the last element (must be a number)

        string action;
        bool action_found = false;
        char lookahead = input_string_with_dollar[input_ptr];
         if (action_table.count(current_state)) {
            const auto& state_actions = action_table.at(current_state);
            if (state_actions.count(lookahead)) {
                action = state_actions.at(lookahead);
                action_found = true;
            }
         }

        // Format stack and input *before* performing the action
        ostringstream stack_oss;
        stack_oss << "[";
        for(size_t j=0; j<stack.size(); ++j) {
            stack_oss << stack[j] << (j == stack.size()-1 ? "" : " ");
        }
        stack_oss << "]";
        string stack_str = stack_oss.str();
        string remaining_input = input_string_with_dollar.substr(input_ptr);

        if (!action_found) {
            vector<string> step = {stack_str, remaining_input, "Error: No action"};
            parse_steps.push_back(step);
            cerr << "Parse Error: No action defined for state " << current_state << " and lookahead '" << lookahead << "' at input position " << input_ptr << endl;
            return false;
        }

        // Record the step
        vector<string> step = {stack_str, remaining_input, action};
        parse_steps.push_back(step);

        // Perform the action
        if (action == "Accept") {
            return true;
        } else if (action[0] == 'S') {
            int target_state = stoi(action.substr(1));
            char current_symbol = lookahead;
            stack.push_back(string(1, current_symbol)); // Push the shifted symbol
            stack.push_back(to_string(target_state));    // Push the target state
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
             if (rhs == string(1, EPSILON)) rhs = "";
            char lhs_non_terminal = production_rule[0];

            int pop_count = rhs.length(); // Number of symbols in RHS
            int items_to_pop = 2 * pop_count; // Pop symbol and state for each RHS element

             if (stack.size() < (size_t)(items_to_pop + 1)) {
                 throw runtime_error("Internal Error: Stack underflow during reduce pop for rule " + production_rule);
             }
            for (int k = 0; k < items_to_pop; ++k) {
                stack.pop_back();
            }

             if (stack.empty()) {
                 throw runtime_error("Internal Error: Stack became empty unexpectedly after popping for reduce.");
             }
            int exposed_state = stoi(stack.back()); // State revealed after popping

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
                 cerr << "Parse Error: Undefined GOTO for state " << exposed_state << " and non-terminal '" << lhs_non_terminal << "'" << endl;
                 // Add error step before returning false
                 vector<string> err_step = {stack_str, remaining_input, "Error: Undefined GOTO"};
                 parse_steps.push_back(err_step);
                return false;
            }

            stack.push_back(string(1, lhs_non_terminal)); // Push LHS symbol
            stack.push_back(to_string(goto_state));        // Push GOTO state

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
        } else if (comp_name.length() > 0 && comp_name.back() != '_') {
             comp_name += '_';
        }
    }
    if (!comp_name.empty() && comp_name.back() == '_') {
        comp_name.pop_back();
    }
     if (comp_name.length() > 50) {
         comp_name = comp_name.substr(0, 50);
     }
    return comp_name.empty() ? "default" : comp_name;
}

void save_file(const string &content, int grammar_num, const string &name_suffix) {
    try {
        string directory = "parsable_strings/" + to_string(grammar_num) + "/";
        fs::create_directories(directory);

        string filename = directory + name_suffix + "_clr1.txt"; // Indicate CLR(1) in filename
        ofstream f(filename);
        if (!f) {
            cerr << "Error: Could not open file for writing: " << filename << endl;
            return;
        }
        f << content;
        f.close();
        cout << "Output saved to " << filename << "\n";
    } catch (const fs::filesystem_error& e) {
        cerr << "Filesystem error when saving file: " << e.what() << endl;
    } catch (const exception& e) {
         cerr << "Error saving file: " << e.what() << endl;
    }
}

string format_table_to_string(const vector<vector<string>>& data, const vector<string>& header) {
     if (header.empty() && data.empty()) return "Table is empty.\n";
     size_t num_cols = header.empty() ? (data.empty() ? 0 : data[0].size()) : header.size();
     if (num_cols == 0) return "Table has no columns.\n";

     vector<size_t> col_widths(num_cols, 0);

     for (size_t j = 0; j < num_cols; ++j) {
         if (j < header.size()) {
            col_widths[j] = max(col_widths[j], header[j].length());
         } else {
             col_widths[j] = 4;
         }
     }
     for (const auto& row : data) {
         for (size_t j = 0; j < num_cols; ++j) {
            if (j < row.size()) {
                col_widths[j] = max(col_widths[j], row[j].length());
            }
         }
     }

     // Specific width adjustment for Stack and Input Buffer if they exist
     size_t stack_col_idx = string::npos;
     size_t input_col_idx = string::npos;
     if (!header.empty()) {
         for (size_t j = 0; j < header.size(); ++j) {
             if (header[j] == "Stack") stack_col_idx = j;
             else if (header[j] == "Input Buffer") input_col_idx = j;
         }
         if (stack_col_idx != string::npos) col_widths[stack_col_idx] = max(col_widths[stack_col_idx], (size_t)15); // Min width for stack
         if (input_col_idx != string::npos) col_widths[input_col_idx] = max(col_widths[input_col_idx], (size_t)15); // Min width for input buffer
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
              bool right_align = false;
              if (!header.empty() && j < header.size()) {
                  if (header[j] == "State") right_align = true; // Right-align state numbers in table
                   // Heuristic: Right-align numbers/shifts/reduces in Action/Goto table
                   else if (header[j] != "Stack" && header[j] != "Input Buffer" && header[j] != "Action") {
                        if (!cell.empty() && (isdigit(cell[0]) || ((cell[0]=='S' || cell[0]=='r') && cell.length() > 1 && all_of(cell.begin() + 1, cell.end(), ::isdigit)))) {
                             right_align = true;
                        }
                   }
                   // Default left align for Stack, Input Buffer, Action in parse steps table
              } else if (!cell.empty() && all_of(cell.begin(), cell.end(), ::isdigit)) { // Fallback if no header
                  right_align = true;
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

void print_clr1_state(int state_id, const vector<Clr1Item>& state) {
    cout << "State " << state_id << ":\n";
    if (state.empty()) {
        cout << "  (empty)\n";
        return;
    }
    for (const auto& item : state) { // Use the state directly as it should be sorted
        cout << "  [" << item.first << ", " << item.second << "]\n";
    }
}


int main() {
    try {
        cout << "CLR(1) Parser Generator and Parser\n";
        cout << "===================================\n";
        cout << "Note: Use '" << EPSILON << "' to represent epsilon productions (e.g., A->" << EPSILON << ").\n";

        int grammar_num;
        cout << "Enter grammar number: ";
        cin >> grammar_num;
        cin.ignore(numeric_limits<streamsize>::max(), '\n');

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
            line.erase(0, line.find_first_not_of(" \t\n\r\f\v"));
            line.erase(line.find_last_not_of(" \t\n\r\f\v") + 1);
            if (!line.empty() && line.rfind("//", 0) != 0) {
                original_grammar.push_back(line);
                cout << "  " << line << endl;
            }
        }
        grammar_file.close();

        if (original_grammar.empty()) {
             cerr << "Error: Grammar file is empty or contains no valid productions." << endl;
             return 1;
        }

        if (!isupper(original_grammar[0][0])) {
             cerr << "Error: First rule's LHS must be an uppercase non-terminal (start symbol)." << endl;
             return 1;
        }
        string start_symbol_str(1, original_grammar[0][0]);
        string augmented_start_rule_no_dot = "X->" + start_symbol_str;

        cout << "\nAugmented Start Rule (for initial state): " << augmented_start_rule_no_dot << " (Lookahead: $)" << endl;
        cout << "---------------------------------------------------------------\n";

        cout << "Computing Terminals, Non-Terminals, and FIRST sets...\n";
        set<char> terminals = get_terminals(original_grammar);
        set<char> non_terminals = get_non_terminals(original_grammar);

        if (terminals.count(EPSILON)) {
            cout << "Info: Epsilon ('" << EPSILON << "') found as a terminal/production RHS.\n";
        } else {
             cout << "Info: Epsilon ('" << EPSILON << "') not explicitly found. Assuming non-epsilon grammar unless rules like A-> exist.\n";
        }


        map<char, set<char>> first_sets = compute_first_sets(original_grammar, non_terminals, terminals);

        cout << "\nFIRST Sets:\n";
        vector<char> nt_sorted(non_terminals.begin(), non_terminals.end()); sort(nt_sorted.begin(), nt_sorted.end()); // Sort for consistent output
        for(char nt : nt_sorted) {
            cout << "  FIRST(" << nt << ") = { ";
            string delim = "";
            vector<char> f_sorted(first_sets[nt].begin(), first_sets[nt].end()); sort(f_sorted.begin(), f_sorted.end()); // Sort set elements
            for(char f : f_sorted) { cout << delim << f; delim = ", "; }
            cout << " }\n";
        }
         cout << "---------------------------------------------------------------\n";


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


         cout << "Building CLR(1) Action and Goto Tables...\n";
        map<int, map<char, string>> action_table;
        map<int, map<char, int>> goto_table;
        build_parsing_table(canonical_collection, dfa_goto, original_grammar, augmented_start_rule_no_dot,
                             terminals, non_terminals, action_table, goto_table);

        vector<string> terminals_sorted;
        for (char t : terminals) terminals_sorted.push_back(string(1, t));
        sort(terminals_sorted.begin(), terminals_sorted.end());

        vector<string> non_terminals_sorted;
        for(char nt : non_terminals) non_terminals_sorted.push_back(string(1, nt));
        sort(non_terminals_sorted.begin(), non_terminals_sorted.end());


        vector<string> table_header = {"State"};
        table_header.insert(table_header.end(), terminals_sorted.begin(), terminals_sorted.end());
        table_header.insert(table_header.end(), non_terminals_sorted.begin(), non_terminals_sorted.end());

         vector<vector<string>> table_data;
         for (int i = 0; i < canonical_collection.size(); ++i) {
             vector<string> row;
             row.push_back(to_string(i));
             for (const string& term_str : terminals_sorted) {
                  char term = term_str[0];
                 if (action_table.count(i) && action_table.at(i).count(term)) {
                     row.push_back(action_table.at(i).at(term));
                 } else {
                     row.push_back("");
                 }
             }
             for (const string& non_term_str : non_terminals_sorted) {
                 char non_term = non_term_str[0];
                  if (goto_table.count(i) && goto_table.at(i).count(non_term)) {
                      row.push_back(to_string(goto_table.at(i).at(non_term)));
                  } else {
                      row.push_back("");
                  }
             }
             table_data.push_back(row);
         }

         cout << "\nCLR(1) Parsing Table (Action | Goto):\n"; // Title updated
         string table_string = format_table_to_string(table_data, table_header);
         cout << table_string;
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

        vector<string> parse_header = {"Stack", "Input Buffer", "Action"}; // Updated header
        string parsing_steps_table = format_table_to_string(parse_steps, parse_header);
        cout << "Parsing Steps:\n";
        cout << parsing_steps_table;
        cout << "---------------------------------------------------------------\n";


        string file_content_to_save;
        file_content_to_save += "Grammar File: " + grammar_filename + "\n";
        file_content_to_save += "Input String: " + input_string + "\n\n";
        file_content_to_save += "CLR(1) Parsing Table:\n"; // Title updated
        file_content_to_save += table_string + "\n";
        file_content_to_save += "Parsing Steps:\n";
        file_content_to_save += parsing_steps_table + "\n";


        if (accepted) {
            cout << "Result: SUCCESS! String \"" << input_string << "\" is accepted by the CLR(1) grammar.\n"; // Updated
            file_content_to_save += "Result: ACCEPTED\n";
            string compressed_name = compress_name(input_string);
            string filename_suffix = compressed_name.empty() ? "accepted_string" : compressed_name;
            save_file(file_content_to_save, grammar_num, filename_suffix); // Uses _clr1.txt suffix now
        } else {
            cout << "Result: FAILURE! String \"" << input_string << "\" is rejected by the CLR(1) grammar.\n"; // Updated
            file_content_to_save += "Result: REJECTED\n";
             string compressed_name = compress_name(input_string);
             string filename_suffix = (compressed_name.empty() ? "rejected_string" : compressed_name) + "_rejected";
             save_file(file_content_to_save, grammar_num, filename_suffix); // Uses _clr1.txt suffix now
        }

    } catch (const fs::filesystem_error& e) {
        cerr << "\nFilesystem Error: " << e.what() << endl;
        cerr << "Please ensure the 'grammar' directory exists and contains the required file." << endl;
        cerr << "Also check permissions for creating the 'parsable_strings' directory." << endl;
        return 1;
    }

    return 0;
}