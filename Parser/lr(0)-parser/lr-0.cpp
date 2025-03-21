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


//TODO there is a segmentation fault in the function find

using namespace std;
namespace fs = std::filesystem;

// Global variable as in the original Python code
vector<string> prod;

// Function: append_dot
// Replaces "->" with "->." in the given string.
string append_dot(const string &a) {
    string jj = a;
    size_t pos = 0;
    while ((pos = jj.find("->", pos)) != string::npos) {
        // Insert a dot after "->"
        jj.insert(pos + 2, ".");
        pos += 3; // Move past the inserted dot
    }
    return jj;
}

// Function: compress_name
// Uses a counter for each character in name and returns a compressed string.
string compress_name(const string &name) {
    map<char, int> res;
    for (char c : name) {
        res[c]++;
    }
    string comp = "";
    for (auto &p : res) {
        comp += p.first + to_string(p.second);
    }
    return comp;
}

// Function: save_file
// Saves final_string to the file "parsable_strings/{grammar}/{name}.txt"
void save_file(const string &final_string, int grammar, const string &name) {
    string directory = "parsable_strings/" + to_string(grammar) + "/";
    // Create directory if it doesn't exist
    if (!fs::exists(directory)) {
        fs::create_directories(directory);
    }
    ostringstream oss;
    oss << directory << name << ".txt";
    ofstream f(oss.str());
    f << final_string;
    f.close();
}

// Function: closure
// Performs the closure operation on a production string.
vector<string> closure(const string &a) {
    vector<string> temp;
    temp.push_back(a);
    // Iterate over temp. Using index-based loop to mimic dynamic growth.
    for (size_t idx = 0; idx < temp.size(); idx++) {
        string it = temp[idx];
        size_t dotPos = it.find(".");
        // If no dot found, continue
        if (dotPos == string::npos || dotPos + 1 >= it.size())
            continue;
        char jj = it[dotPos + 1];
        // Check if dot is not at the end
        if (dotPos != it.size() - 1) {
            for (auto &k : prod) {
                // k[0] corresponds to the first character of k.
                if (!k.empty() && k[0] == jj) {
                    string newprod = append_dot(k);
                    // Check if newprod is not already in temp
                    if (find(temp.begin(), temp.end(), newprod) == temp.end()) {
                        temp.push_back(newprod);
                    }
                }
            }
        } else {
            for (auto &k : prod) {
                if (!k.empty() && k[0] == jj) {
                    if (find(temp.begin(), temp.end(), it) == temp.end()) {
                        temp.push_back(it);
                    }
                }
            }
        }
    }
    return temp;
}

// Function: swap
// Swaps the character at position pos with the next character if possible.
string swap_chars(const string &newStr, int pos) {
    string newString = newStr;
    if (pos < (int)newString.size() - 1) {
        char temp = newString[pos];
        newString[pos] = newString[pos + 1];
        newString[pos + 1] = temp;
        return newString;
    } else {
        return newString;
    }
}

// Function: goto1
// Returns the goto result for production x1 as a vector of strings.
vector<string> goto1(const string &x1) {
    vector<string> ret;
    size_t pos = x1.find(".");
    if (pos != string::npos && pos != x1.size() - 1) {
        string kk = swap_chars(x1, pos);
        size_t newPos = kk.find(".");
        if (newPos != string::npos && newPos != kk.size() - 1) {
            vector<string> jjj = closure(kk);
            return jjj;
        } else {
            ret.push_back(kk);
            return ret;
        }
    } else {
        ret.push_back(x1);
        return ret;
    }
}

// Function: get_terminals
// Returns a set of terminals from the grammar productions.
set<char> get_terminals(const vector<string> &gram) {
    set<char> terms;
    for (auto &p : gram) {
        size_t arrowPos = p.find("->");
        if (arrowPos == string::npos) continue;
        string right = p.substr(arrowPos + 2);
        // Trim spaces from the right part
        right.erase(remove(right.begin(), right.end(), ' '), right.end());
        for (char t : right) {
            if (!isupper(t) && t != '.' && t != '\0') {
                terms.insert(t);
            }
        }
    }
    terms.insert('$');
    return terms;
}

// Function: get_non_terminals
// Returns a set of non-terminals from the grammar productions.
set<char> get_non_terminals(const vector<string> &gram) {
    set<char> terms;
    for (auto &p : gram) {
        size_t arrowPos = p.find("->");
        if (arrowPos == string::npos) continue;
        string right = p.substr(arrowPos + 2);
        right.erase(remove(right.begin(), right.end(), ' '), right.end());
        for (char t : right) {
            if (isupper(t)) {
                terms.insert(t);
            }
        }
    }
    return terms;
}

// Function: get_list
// Returns a list of strings from graph whose first token (state number) equals the given state.
vector<string> get_list(const vector<string> &graph, int state) {
    vector<string> final_list;
    for (auto &g : graph) {
        istringstream iss(g);
        string token;
        iss >> token;
        try {
            int st = stoi(token);
            if (st == state) {
                final_list.push_back(g);
            }
        } catch (exception &e) {
            // Do nothing if conversion fails
        }
    }
    return final_list;
}

// Helper function: join a vector of strings with a separator (used for table header concatenation)
vector<string> join_vectors(const vector<string>& v1, const vector<string>& v2) {
    vector<string> res = v1;
    res.insert(res.end(), v2.begin(), v2.end());
    return res;
}

// Function: to_string_table
// Mimics termtables.to_string to format a table with headers and data
string to_string_table(const vector<vector<string>> &data, const vector<string> &header, const pair<int,int> &padding) {
    // Calculate number of columns
    size_t cols = header.size();
    vector<size_t> colWidths(cols, 0);
    
    // Consider header widths
    for (size_t j = 0; j < cols; j++) {
        colWidths[j] = header[j].size();
    }
    // Consider each data row
    for (auto &row : data) {
        for (size_t j = 0; j < row.size(); j++) {
            colWidths[j] = max(colWidths[j], row[j].size());
        }
    }
    // Build the table string with ascii borders
    ostringstream oss;
    string padLeft(padding.first, ' ');
    string padRight(padding.second, ' ');
    
    // Top border
    oss << "+";
    for (size_t j = 0; j < cols; j++) {
        oss << string(colWidths[j] + padLeft.size() + padRight.size(), '-') << "+";
    }
    oss << "\n";
    
    // Header row
    oss << "|";
    for (size_t j = 0; j < cols; j++) {
        int totalSpace = colWidths[j] - header[j].size();
        int leftSpace = totalSpace / 2;
        int rightSpace = totalSpace - leftSpace;
        oss << padLeft << string(leftSpace, ' ') << header[j] << string(rightSpace, ' ') << padRight << "|";
    }
    oss << "\n";
    
    // Separator
    oss << "+";
    for (size_t j = 0; j < cols; j++) {
        oss << string(colWidths[j] + padLeft.size() + padRight.size(), '-') << "+";
    }
    oss << "\n";
    
    // Data rows
    for (auto &row : data) {
        oss << "|";
        for (size_t j = 0; j < cols; j++) {
            string cell = (j < row.size() ? row[j] : "");
            int totalSpace = colWidths[j] - cell.size();
            int leftSpace = totalSpace / 2;
            int rightSpace = totalSpace - leftSpace;
            oss << padLeft << string(leftSpace, ' ') << cell << string(rightSpace, ' ') << padRight << "|";
        }
        oss << "\n";
    }
    
    // Bottom border
    oss << "+";
    for (size_t j = 0; j < cols; j++) {
        oss << string(colWidths[j] + padLeft.size() + padRight.size(), '-') << "+";
    }
    return oss.str();
}

int main(){
    try {
        // Display ASCII art using a placeholder for pyfiglet.figlet_format
        // In the original code, pyfiglet is used to generate large ASCII text.
        // Here we output a hard-coded version.
        string result = "LR(0) Parser : ";
        cout << result << "\n";

        vector<string> prod_vec; // Already declared globally as 'prod'
        vector<vector<string>> set_of_items;
        vector<vector<string>> c;
        
        map<string, int> prod_num;
        int num;
        cout << "Enter grammar number: ";
        cin >> num;
        cin.ignore(); // clear newline
        cout << "\n";
        
        // Read grammar file "grammar/{num}.txt"
        {
            ostringstream fileName;
            fileName << "grammar/" << num << ".txt";
            ifstream fp(fileName.str());
            string line;
            while(getline(fp, line)) {
                // Trim the line (if needed)
                if(!line.empty()) {
                    prod.push_back(line);
                }
            }
        }
        
        // Insert the augmented production at the beginning.
        prod.insert(prod.begin(), "X->.S");
        cout << "---------------------------------------------------------------" << "\n";
        cout << "Augmented Grammar" << "\n";
        // Print augmented grammar
        cout << "[";
        for (size_t i = 0; i < prod.size(); i++){
            cout << prod[i];
            if(i < prod.size()-1)
                cout << ", ";
        }
        cout << "]" << "\n";
        
        // Build prod_num mapping: production string -> index (starting from 1)
        for (size_t i = 1; i < prod.size(); i++) {
            prod_num[prod[i]] = i;
        }
        
        // Compute closure for initial production "X->.S"
        vector<string> j = closure("X->.S");
        set_of_items.push_back(j);
        
        // Prepare state_numbers and dfa_prod
        map<string, int> state_numbers;
        vector<string> dfa_prod_keys; // For later iteration tracking keys in order.
        map<string, vector<string>> dfa_prod;
        int items = 0;
        
        // Main loop to build set_of_items and dfa_prod.
        while (true) {
            if (set_of_items.empty())
                break;
            vector<string> jk = set_of_items.front();
            set_of_items.erase(set_of_items.begin());
            vector<string> kl = jk;
            c.push_back(jk);
            // Use string representation of jk as key. We join elements with a delimiter.
            ostringstream oss_state;
            for (auto &s : jk) {
                oss_state << s << "|";
            }
            string stateKey = oss_state.str();
            state_numbers[stateKey] = items;
            items++;
            
            if (jk.size() > 1) {
                for (auto &item : jk) {
                    vector<string> jl = goto1(item);
                    // Check if jl is not in set_of_items and not equal to kl.
                    bool foundInSet = false;
                    // Compare as joined string
                    ostringstream oss_jl;
                    for (auto &s : jl) oss_jl << s << "|";
                    string jlKey = oss_jl.str();
                    ostringstream oss_kl;
                    for (auto &s : kl) oss_kl << s << "|";
                    string klKey = oss_kl.str();
                    for (auto &exist : set_of_items) {
                        ostringstream oss_exist;
                        for (auto &s : exist) oss_exist << s << "|";
                        if(oss_exist.str() == jlKey) {
                            foundInSet = true;
                            break;
                        }
                    }
                    if (!foundInSet && jlKey != klKey) {
                        set_of_items.push_back(jl);
                    }
                    // Record in dfa_prod with key: (state_numbers[jk] as string + " " + item)
                    string key = to_string(state_numbers[stateKey]) + " " + item;
                    dfa_prod[key] = jl;
                }
            }
        }
        
        // Second loop to add additional items based on goto1 of items in c
        for (auto &itemList : c) {
            for (size_t j_index = 0; j_index < itemList.size(); j_index++) {
                vector<string> tempGoto = goto1(itemList[j_index]);
                // Check if this result is not already in c (compare as joined string)
                ostringstream oss_tempGoto;
                for (auto &s : tempGoto) oss_tempGoto << s << "|";
                string tempGotoKey = oss_tempGoto.str();
                bool exists = false;
                for (auto &existing : c) {
                    ostringstream oss_exist;
                    for (auto &s : existing) oss_exist << s << "|";
                    if(oss_exist.str() == tempGotoKey) {
                        exists = true;
                        break;
                    }
                }
                size_t dotPos = itemList[j_index].find(".");
                if (dotPos != string::npos && dotPos != itemList[j_index].size()-1 && !exists) {
                    c.push_back(tempGoto);
                }
            }
        }
        
        cout << "---------------------------------------------------------------" << "\n";
        cout << "Total States: " << c.size() << "\n";
        for (size_t i = 0; i < c.size(); i++) {
            cout << i << " : ";
            cout << "[";
            for (size_t j = 0; j < c[i].size(); j++) {
                cout << c[i][j];
                if(j < c[i].size()-1)
                    cout << ", ";
            }
            cout << "]" << "\n";
        }
        cout << "---------------------------------------------------------------" << "\n";
        
        // Build DFA mapping
        map<int, map<string, int>> dfa;
        for (size_t i = 0; i < c.size(); i++) {
            if (dfa.find(i) == dfa.end()) {
                vector<string> lst;
                // Get keys from dfa_prod that correspond to state i
                // dfa_prod keys are in format "i <space> production"
                for (auto &entry : dfa_prod) {
                    istringstream iss(entry.first);
                    int stateNum;
                    iss >> stateNum;
                    if (stateNum == (int)i) {
                        lst.push_back(entry.first);
                    }
                }
                map<string, int> samp;
                for (auto &jstr : lst) {
                    // jstr is in format "state production"
                    size_t spacePos = jstr.find(" ");
                    string productionPart = jstr.substr(spacePos+1);
                    // Split productionPart by "->" and then take right side.
                    size_t arrowPos = productionPart.find("->");
                    if (arrowPos != string::npos) {
                        string s = productionPart.substr(arrowPos+2);
                        // Remove spaces
                        s.erase(remove(s.begin(), s.end(), ' '), s.end());
                        size_t dotIndex = s.find(".");
                        if (dotIndex != string::npos && dotIndex + 1 < s.size()) {
                            string search(1, s[dotIndex+1]);
                            // Get state number from dfa_prod for key jstr
                            ostringstream keyStream;
                            keyStream << i << " " << productionPart;
                            // Retrieve corresponding goto vector from dfa_prod map using the key jstr
                            string key = jstr;
                            vector<string> gotoVal = dfa_prod[key];
                            // Build key for state_numbers from gotoVal vector
                            ostringstream oss_state2;
                            for (auto &s2 : gotoVal) {
                                oss_state2 << s2 << "|";
                            }
                            string gotoKey = oss_state2.str();
                            int targetState = state_numbers[gotoKey];
                            samp[search] = targetState;
                        }
                    }
                }
                if (!samp.empty()) {
                    dfa[i] = samp;
                }
            }
        }
        
        // Generate parsing table
        vector<vector<string>> table;
        
        // Get terminals and sort them
        set<char> termSet = get_terminals(prod);
        vector<string> term;
        for (char c : termSet) {
            term.push_back(string(1, c));
        }
        sort(term.begin(), term.end());
        
        vector<string> header;
        header.resize(term.size() + 1, "");
        header[(term.size() + 1) / 2] = "Action";
        
        // Get non-terminals and sort them
        set<char> nonTermSet = get_non_terminals(prod);
        vector<string> non_term;
        for (char c : nonTermSet) {
            non_term.push_back(string(1, c));
        }
        sort(non_term.begin(), non_term.end());
        vector<string> header2;
        header2.resize(non_term.size(), "");
        if(!non_term.empty())
            header2[(non_term.size()) / 2] = "Goto";
        
        // First row of table: concatenation of "" + term + non_term
        vector<string> firstRow;
        firstRow.push_back("");
        for (auto &t : term) {
            firstRow.push_back(t);
        }
        for (auto &nt : non_term) {
            firstRow.push_back(nt);
        }
        table.push_back(firstRow);
        
        // table_dic mapping: state -> mapping of symbol -> action
        map<int, map<string, string>> table_dic;
        
        // For each state i
        for (size_t i = 0; i < c.size(); i++) {
            vector<string> data_row;
            data_row.resize(term.size() + non_term.size(), "");
            map<string, string> samp;
            try {
                // Action part
                if (dfa.find(i) != dfa.end()) {
                    for (auto &entry : dfa[i]) {
                        string j = entry.first;
                        // Check if j is not uppercase, not empty and not "."
                        if (!j.empty() && !isupper(j[0]) && j != "." && j != "") {
                            // Find index in term vector
                            auto it = find(term.begin(), term.end(), j);
                            if (it != term.end()) {
                                int ind = distance(term.begin(), it);
                                data_row[ind] = "S" + to_string(entry.second);
                                samp[term[ind]] = "S" + to_string(entry.second);
                            }
                        }
                    }
                }
            } catch (exception &e) {
                if (i != 1) {
                    // Get production from c[i][0], remove '.'
                    string s = c[i][0];
                    s.erase(remove(s.begin(), s.end(), '.'), s.end());
                    vector<string> lst;
                    lst.push_back(to_string(i));
                    // Add 'r' + prod_num for each terminal in term
                    for (size_t k = 0; k < term.size(); k++) {
                        lst.push_back("r" + to_string(prod_num[s]));
                    }
                    // Add empty strings for non_term part
                    for (size_t k = 0; k < non_term.size(); k++) {
                        lst.push_back("");
                    }
                    table.push_back(lst);
                    for (auto &t : term) {
                        samp[t] = "r" + to_string(prod_num[s]);
                    }
                } else {
                    vector<string> lst;
                    lst.push_back(to_string(i));
                    for (size_t k = 0; k < term.size() + non_term.size(); k++) {
                        lst.push_back("");
                    }
                    lst[lst.size()-1] = "Accept";
                    table.push_back(lst);
                }
            }
            
            // Goto part
            try {
                if (dfa.find(i) != dfa.end()) {
                    for (auto &entry : dfa[i]) {
                        string j = entry.first;
                        if (!j.empty() && isupper(j[0])) {
                            auto it = find(non_term.begin(), non_term.end(), string(1, j[0]));
                            if (it != non_term.end()) {
                                int ind = distance(non_term.begin(), it);
                                data_row[term.size() + ind] = to_string(entry.second);
                                samp[j] = to_string(entry.second);
                            }
                        }
                    }
                    // Append the row: state number followed by data_row contents.
                    vector<string> row;
                    row.push_back(to_string(i));
                    for (auto &d : data_row) {
                        row.push_back(d);
                    }
                    table.push_back(row);
                }
            } catch (exception &e) {
                // Do nothing if exception occurs.
            }
            
            if (samp.empty()) {
                table_dic[i] = { {"$", "Accept"} };
            } else {
                table_dic[i] = samp;
            }
        }
        
        // Create final header for table: header + header2
        vector<string> fullHeader = join_vectors(header, header2);
        string final_table = to_string_table(table, fullHeader, {0, 1});
        
        cout << "\n" << final_table << "\n\n";
        
        // Parse String
        cout << "Enter the string to be parsed: ";
        string inputString;
        getline(cin, inputString);
        if(inputString == "")
            getline(cin, inputString);
        inputString += "$";
        cout << "\n";
        
        vector<int> stack;
        stack.push_back(0);
        int pointer = 0;
        
        vector<vector<string>> parse_data;
        int i_index = 0;
        bool accepted = false;
        
        while (true) {
            try {
                int currentState = stack.back();
                int prod_i = -1;
                // Attempt to get production from dfa based on lookahead symbol
                map<string, int> prods;
                if (dfa.find(currentState) != dfa.end()) {
                    prods = dfa[currentState];
                }
                // Convert lookahead symbol to string
                string lookahead(1, inputString[i_index]);
                if (prods.find(lookahead) != prods.end()) {
                    prod_i = prods[lookahead]; // state number
                } else {
                    prod_i = -1;
                }
                
                string tab_i = "";
                try {
                    map<string, string> tab = table_dic[currentState];
                    if (tab.find(lookahead) != tab.end()) {
                        tab_i = tab[lookahead];
                    } else {
                        throw runtime_error("Not found");
                    }
                } catch (exception &e) {
                    // If error, try using previous state
                    if (stack.size() >= 2) {
                        int prevState = stack[stack.size()-2];
                        map<string, string> tab = table_dic[prevState];
                        string stateSymbol = to_string(currentState);
                        if (tab.find(stateSymbol) != tab.end()) {
                            tab_i = tab[stateSymbol];
                        }
                    }
                }
                
                // Record processing step in parse_data
                vector<string> lst;
                lst.push_back("Action(" + to_string(currentState) + ", " + lookahead + ") = " + tab_i);
                lst.push_back(to_string(i_index));
                lst.push_back(lookahead);
                lst.push_back("[");
                for (size_t j = 0; j < stack.size(); j++) {
                    lst.back() += to_string(stack[j]);
                    if(j < stack.size()-1) lst.back() += ", ";
                }
                lst.back() += "]";
                
                if (tab_i == "Accept") {
                    parse_data.push_back(lst);
                    accepted = true;
                    break;
                } else {
                    if (!tab_i.empty() && tab_i[0] == 'S') {
                        // Shift operation
                        stack.push_back((prod_i));
                        // Also push the symbol from the input onto the stack.
                        // In the Python code, they push the lookahead symbol.
                        // We do not push non-integer so we ignore state check of isupper() on state.
                        // For completeness, we simulate the behavior.
                        // (We push the lookahead symbol as a dummy marker; we won't use it for state numbers.)
                        // Here we simply continue.
                        parse_data.push_back(lst);
                        i_index++;
                    } else if (!tab_i.empty() && tab_i[0] == 'r') {
                        // Reduce operation
                        string x = "";
                        // Find production from prod_num with number equal to the digit after 'r'
                        int prodNumber = stoi(tab_i.substr(1));
                        for (auto &p : prod_num) {
                            if (p.second == prodNumber) {
                                x = p.first;
                                break;
                            }
                        }
                        // Calculate length = 2 * (length of right-hand side of production)
                        size_t arrowPos = x.find("->");
                        string rhs = "";
                        if (arrowPos != string::npos) {
                            rhs = x.substr(arrowPos+2);
                            // Remove dots if any.
                            rhs.erase(remove(rhs.begin(), rhs.end(), '.'), rhs.end());
                        }
                        int length = 2 * rhs.size();
                        for (int k = 0; k < length && !stack.empty(); k++) {
                            stack.pop_back();
                        }
                        // Push left-hand side symbol of production x
                        if (!x.empty()) {
                            stack.push_back((int)x[0]); // storing ASCII code for non-terminal
                        }
                        parse_data.push_back(lst);
                    } else {
                        // Goto handling
                        // Use previous two elements in the stack.
                        string gotoAction = "goto(" + to_string(stack[stack.size()-2]) + ", " + to_string(stack.back()) + ") = " + tab_i;
                        vector<string> lst2;
                        lst2.push_back(gotoAction);
                        lst2.push_back(to_string(i_index));
                        lst2.push_back(lookahead);
                        lst2.push_back("[");
                        for (size_t j = 0; j < stack.size(); j++) {
                            lst2.back() += to_string(stack[j]);
                            if(j < stack.size()-1) lst2.back() += ", ";
                        }
                        lst2.back() += "]";
                        parse_data.push_back(lst2);
                        // Push the state from tab_i
                        int state_to_push = stoi(tab_i);
                        stack.push_back(state_to_push);
                    }
                }
            } catch (exception &e) {
                accepted = false;
                break;
            }
        }
        
        try {
            vector<string> parseHeader = {"Process", "Look Ahead", "Symbol", "Stack"};
            string parsing_table = to_string_table(parse_data, parseHeader, {0, 1});
            if (accepted) {
                // Remove the appended '$' from the input string for output.
                string originalString = inputString.substr(0, inputString.size()-1);
                string compressed_name = compress_name(originalString);
                save_file(parsing_table, num, compressed_name);
                cout << "The string " << originalString << " is parsable! Please find the parsing table in "
                     << "parsable_strings/" << num << "/" << compressed_name << ".txt." << "\n";
            } else {
                cout << "The string " << inputString << " is not parsable!" << "\n";
            }
        } catch (exception &e) {
            cout << "Invalid string entered!" << "\n";
        }
    } catch (exception &e) {
        cout << "An error occurred: " << e.what() << "\n";
    }
    return 0;
}
  
