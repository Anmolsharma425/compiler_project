// g++ -std=c++11 -o 220010062 220010062.cpp
// ./220010062
// then enter input expression you want to check on terminal when promted

#include <iostream>
#include <string>
#include <stack>
#include <vector>
#include <cctype>
#include <iomanip>
using namespace std;

#define WINDOW_SIZE 40

struct production{
    int index;
    string lhs;
    string rhs;
        production(int idx, string lhs, string rhs) {
            this->index = idx;  
            this->lhs = lhs;
            this->rhs = rhs;
        }
};

string preprocess(string word){
    string result;
    int n = word.length();
    int i = 0;

    while (i < n) {
        if (isdigit(word[i])) {
            // while (i < n && isdigit(word[i])) {
            //     i++;
            // }
            result += 'I';
            i++;
        } else if (word[i] == ' ') {
            i++; // skip spaces
        } else {
            result += word[i++];
        }
    }

    result += '$'; // Append end marker
    return result;
}

int getOperatorIndex(char op) {
    switch (op) {
        case '+': return 0;
        case '-': return 1;
        case '*': return 2;
        case '/': return 3;
        case '(': return 4;
        case ')': return 5;
        case 'I': return 6; // Operand
        case '$': return 7; // End of input
        default: return -1; // Invalid operator
    }
}

char getTopTerminal(stack<char> op_stack) {
    // Skip non-terminals like 'E' to find topmost terminal
    while (!op_stack.empty()) {
        char top = op_stack.top();
        if (top == '+' || top == '-' || top == '*' || top == '/' || top == '(' || top == ')'|| top == 'I' || top == '$') {
            return top;
        }
        op_stack.pop();
    }
    return '$'; // Default fallback
}

void printStack(stack<char> s) {
    vector<char> temp;
    while (!s.empty()) {
        temp.push_back(s.top());
        s.pop();
    }
    for(int i=0;i<temp.size();i++){
        cout << temp[i];
    }   
}

bool handleReduction(stack<char>& operator_stack, vector<production>& grammar) {
    string handle = "";
    stack<char> temp = operator_stack;
    bool reduceable = false;
    char reduce_to;

   while(!temp.empty() && !reduceable){
        handle = temp.top() + handle;
        temp.pop();
        
        // Check for valid reduction handles
        for(const auto& prod : grammar) {
            if (prod.rhs == handle) {
                // operator_stack.push(prod.lhs[0]); // Push lhs
                reduce_to = prod.lhs[0];
                reduceable = true;
            }
        }
    }

    if (reduceable) {
        // Pop the handle from the stack
        for (int j = 0; j < handle.size(); j++) {
            operator_stack.pop();
        }
        operator_stack.push(reduce_to);
        // cout << "Reduced: " << handle << " to " << reduce_to << endl;
        return true;
    }else{
        cout << "Error: No valid reduction found for handle: " << handle << endl;
        return false;
    }
}

void printDebugInfo(stack<char> operator_stack, const string& input, int i, const string& Action){
    string stack_data = "";
    // cout << "Operator Stack: ";
    vector<char> vec;
    while(!operator_stack.empty()) {
        vec.push_back(operator_stack.top());
        operator_stack.pop();
    }
    for(int j = vec.size() - 1; j >= 0; j--){
        // cout << vec[j];
        stack_data += vec[j];
    }
    // cout << "\tRemaining Input: " << input.substr(i) << "\tAction: " << Action << endl;

    cout << left;
    cout << setw(WINDOW_SIZE) << stack_data 
        << setw(WINDOW_SIZE) << input.substr(i) 
        << Action << endl;

}

int main(){

    //Define the grammar
    vector<production> grammar;
    grammar.push_back(production(1,"E", "E+E"));
    grammar.push_back(production(2,"E", "E*E"));
    grammar.push_back(production(3,"E", "E/E"));
    grammar.push_back(production(4,"E", "E-E"));
    grammar.push_back(production(5,"E", "I"));//Changed "INT_LITERAL" to 'I'
    grammar.push_back(production(6,"E", "(E)"));

    //read word 
    string word;
    cout << "Enter a word: ";
    getline(cin, word); //( 3+5*2-8/4)

    cout << "The word you entered is: " << word << endl;

    //followign BODMAS precedence :  I > / > * > + > - > $ 
    //precedence table
    char precedence_table[8][8] = {
        //        +    -    *    /    (    )    I    $ 
        /* + */ {'>', '>', '<', '<', '<', '>', '<', '>'},
        /* - */ {'>', '>', '<', '<', '<', '>', '<', '>'},
        /* * */ {'>', '>', '>', '>', '<', '>', '<', '>'},
        /* / */ {'>', '>', '>', '>', '<', '>', '<', '>'},
        /* ( */ {'<', '<', '<', '<', '<', '=', '<', 'E'},
        /* ) */ {'>', '>', '>', '>', 'E', '>', 'E', '>'},
        /* I */ {'>', '>', '>', '>', 'E', '>', 'E', '>'},  // digit -> I
        /* $ */ {'<', '<', '<', '<', '<', 'E', '<', 'A'}
    };

    //if LHS < RHS then shift
    //if LHS > RHS then reduce

    int i=0;
    string input = preprocess(word);

    cout << "The input string is: " << input << endl;
    string Action;

    stack<char> operator_stack;

    operator_stack.push('$');
    vector<char> operator_vector;
    operator_vector.push_back('$');
    int check = 0;
    bool reduceable  = false;
    bool first = true;

    while(i < input.size()){
        check++;
        if(check > 50){
            cout << "Infinite loop detected" << endl;
            break;
        }
        char top_operator = getTopTerminal(operator_stack);
        char current_char = input[i];

        //get index
        int top_operator_index = getOperatorIndex(top_operator);
        int current_char_index = getOperatorIndex(current_char);
        
        if(top_operator_index == -1 || current_char_index == -1){
            cout << "\nInvalid character in input.\n";
            break;
        }

        if(first){
            cout << endl;
            cout << left;
            cout << setw(WINDOW_SIZE) << "Operator Stack:" 
                << setw(WINDOW_SIZE) << "Remaining Input:" 
                << "Action:" << endl;
            first = false;
        }

        if(precedence_table[top_operator_index][current_char_index] == '<' || precedence_table[top_operator_index][current_char_index] == '='){
            //shift
            Action = "Shift";
            printDebugInfo(operator_stack, input, i, Action);
            operator_stack.push(current_char);
            i++;
        }
        else if(precedence_table[top_operator_index][current_char_index] == '>'){
            //reduce
            Action = "Reduce";
            printDebugInfo(operator_stack, input, i, Action);

            // operator_stack.pop();
            reduceable = handleReduction(operator_stack, grammar);
            if(!reduceable){
                break;
            }
        }
        else if(precedence_table[top_operator_index][current_char_index] == 'E'){
            Action = "Error";
            printDebugInfo(operator_stack, input, i, Action);
            break;
        }
        else if(precedence_table[top_operator_index][current_char_index] == 'A'){
            Action = "Accept";
            printDebugInfo(operator_stack, input, i, Action);
            break;
        }
    }

    cout << endl;

    if(Action == "Accept"){
        cout << "The input string is accepted." << endl;
    }
    else{
        cout << "The input string is not accepted." << endl;
    }

}

/*
E -> E+E
E -> E*E
E -> E-E
E -> E/E
E -> INT_LITERAL
E -> (E)
*/
