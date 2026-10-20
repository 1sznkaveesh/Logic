/*
 Stores a propositional logic formula as a binary parse tree and implements
 all Part-A tasks with a compact, assignment-focused implementation
 The main documentation page is the project README (see Doxyfile)
 Two ways to run the program:
   - `./logic_assignment`                 : type a fully parenthesized infix
                                            formula, e.g. `((P*Q)>~R)`
                                            (Tasks 1 to 6)
  - `./logic_assignment --dimacs FILE.cnf`: load a DIMACS CNF file
                                            (SAT benchmark, Tasks 3 to 6)

 Task 1 (infix -> prefix) tokenizes the input and uses the idea from scanftree.com/Data_Structure/infix-to-prefix :
      1. Reverse the tokens
      2. Swap every '(' with ')' and vice versa
      3. Convert this token sequence to postfix using an operator stack
      4. Reverse the postfix tokens -> this is the prefix expression
 
Task 6 (analysis): every algorithm is timed, its extra memory use is
measured, and the results are printed and saved in analysis_report.html
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <time.h>

#define MAX 500             // Maximum input length
#define MAXPREFIX (2 * MAX) // Maximum prefix expression length
#define MAXTOK MAX          // Maximum number of tokens
#define MAXVARS 200000      // Maximum number of variables
#define NAMELEN 16          // Maximum atom name length
#define ATOM '#'            // Marks a variable node
#define TT_LIMIT 16         // Maximum variables for truth table output
#define SMALL_TREE 60       // Node limit for full tree printing

/* Binary tree node */

// Represents a node in the parse tree
typedef struct Node {
    char symbol;          // Operator or ATOM for a variable
    char name[NAMELEN];   // Variable name
    int var;              // Variable index in varValues[]
    struct Node *left;    // Left child
    struct Node *right;   // Right child
} Node;

// A token can be a variable, operator, or parenthesis
typedef char Token[NAMELEN];

/* Global variables */

int pos;                          // Current position in prefix tokens
int verbose = 1;                  // Enables or disables traversal output
int peakAux = 0;                  // Maximum stack or queue size
int treeSize = 0;                 // Number of nodes in the tree
int treeHeight = 0;               // Height of the tree
int cnfClauses = 0;               // Number of CNF clauses

char varNames[MAXVARS][NAMELEN];  // Names of the variables
int varValues[MAXVARS];           // Truth values of the variables
int varCount = 0;                 // Number of distinct variables

char gInfix[MAX];                 // Original infix formula
Token gPrefixToks[MAXTOK];        // Prefix tokens
int gPrefixCount = 0;             // Number of prefix tokens
char gPrefix[MAXPREFIX];          // Prefix expression as a string
Node *gRoot = NULL;               // Root of the parse tree
long gTrueRows = -1;               // Number of true rows, -1 if skipped
/* ---------------- Basic helpers ---------------- */

// Creates and returns a new tree node
Node *newNode(char symbol, const char *name, Node *left, Node *right) {
    Node *node = (Node *) malloc(sizeof(Node));
    if (node == NULL) {
        fprintf(stderr, "Error: out of memory\n");
        exit(1);
    }
    node->symbol = symbol;
    strncpy(node->name, name, NAMELEN - 1);
    node->name[NAMELEN - 1] = '\0';
    node->var = -1;
    node->left = left;
    node->right = right;
    return node;
}

// Frees all nodes in the tree
void freeTree(Node *root) {
    if (root == NULL) return;
    freeTree(root->left);
    freeTree(root->right);
    free(root);
}

// Checks whether the character is a valid operator
int isOperator(char c) {
    return c == '~' || c == '+' || c == '*' || c == '>';
}

// Returns the precedence of an operator
int precedence(char c) {
    if (c == '~') return 3;
    if (c == '*') return 2;
    if (c == '+') return 1;
    if (c == '>') return 0;
    return -1;
}

// Counts the nodes in the tree
int countNodes(Node *root) {
    if (root == NULL) return 0;
    return 1 + countNodes(root->left) + countNodes(root->right);
}

// Prints a string if output is enabled
void showStr(const char *s) {
    if (verbose) fputs(s, stdout);
}

// Prints a node's symbol or variable name
void showNode(Node *node) {
    if (!verbose) return;
    if (isOperator(node->symbol)) putchar(node->symbol);
    else fputs(node->name, stdout);
}

// Updates the maximum stack or queue size
void track(int size) {
    if (size > peakAux) peakAux = size;
}

/*
============================================================
  TASK 1: Convert infix expression to prefix expression
============================================================
 */

// Prints an error message and exits when the formula is invalid
void invalidFormula(const char *reason) {
    fprintf(stderr, "Invalid formula: %s\n", reason);
    exit(1);
}

/// Splits the input formula into tokens, ignoring spaces and keeping atom names together
int tokenize(const char *str, Token toks[], int maxToks) {
    int n = 0;

    for (int i = 0; str[i] != '\0'; ) {
        char c = str[i];

        if (isspace((unsigned char) c)) {
            i++;
        }
        else if (isOperator(c) || c == '(' || c == ')') {
            if (n >= maxToks) invalidFormula("too many tokens");
            toks[n][0] = c;
            toks[n][1] = '\0';
            n++;
            i++;
        }
        else if (isalpha((unsigned char) c) || c == '_') {
            int len = 0;
            if (n >= maxToks) invalidFormula("too many tokens");
            while (isalnum((unsigned char) str[i]) || str[i] == '_') {
                if (len >= NAMELEN - 1) invalidFormula("atom name is too long");
                toks[n][len++] = str[i++];
            }
            toks[n][len] = '\0';
            n++;
        }
        else {
            invalidFormula("unexpected character");
        }
    }

    if (n == 0) invalidFormula("empty formula");
    return n;
}

// Checks whether all opening and closing parentheses match
int checkParens(Token toks[], int n) {
    int depth = 0;
    for (int i = 0; i < n; i++) {
        if (toks[i][0] == '(') depth++;
        else if (toks[i][0] == ')') {
            depth--;
            if (depth < 0) return 0;
        }
    }
    return depth == 0;
}

// Reverses each opening and closing parenthesis in the token array
void swapParens(Token toks[], int n) {
    for (int i = 0; i < n; i++) {
        if (toks[i][0] == '(') strcpy(toks[i], ")");
        else if (toks[i][0] == ')') strcpy(toks[i], "(");
    }
}

// Converts an infix expression to postfix using an operator stack
void infixToPostfix(Token in[], int n, Token out[], int *outN) {
    Token stack[MAXTOK];
    int top = -1;
    int k = 0;

    for (int i = 0; i < n; i++) {
        char c = in[i][0];

        if (c == '(' && in[i][1] == '\0') {
            strcpy(stack[++top], in[i]);       
        }
        else if (c == ')' && in[i][1] == '\0') {
            while (top >= 0 && strcmp(stack[top], "(") != 0) {
                strcpy(out[k++], stack[top--]);  
            }
            top--;                              
        }
        else if (c == '~' || c == '+' || c == '*' || c == '>') {
            while (top >= 0 && strcmp(stack[top], "(") != 0 &&
                   precedence(stack[top][0]) >= precedence(c)) {
                strcpy(out[k++], stack[top--]);  
            }
            strcpy(stack[++top], in[i]);
        }
        else {
            strcpy(out[k++], in[i]);           
        }
    }

    while (top >= 0) {
        strcpy(out[k++], stack[top--]);
    }
    *outN = k;
}

/*
 1. The purpose of this below block of code is to convert the original infix formula into prefix notation
 2. We first tokenize it , then reverse it , swap the parantheses (like ( is changed to ) and vice versa..), 
    then we convert it to postfix , and finally after reversing again , we get the desired result
 3. this function stores both : the prefix tokens for Task 2 and a printable prefix string
 
 */
void infixToPrefix(const char *infix, Token toks[], int *count, char *text) {
    Token in[MAXTOK];
    int n = tokenize(infix, in, MAXTOK);

    if (!checkParens(in, n)) invalidFormula("unbalanced parentheses");

    Token rev[MAXTOK];
    for (int i = 0; i < n; i++) {                // reverses the tokens 
        strcpy(rev[i], in[n - 1 - i]);
    }
    swapParens(rev, n);

    Token post[MAXTOK];
    int postN = 0;
    infixToPostfix(rev, n, post, &postN);

    for (int i = 0; i < postN; i++) {            // reverse postfix -> prefix 
        strcpy(toks[i], post[postN - 1 - i]);
    }
    *count = postN;

    int needsSpace = 0;
    for (int i = 0; i < postN; i++) {
        if (strlen(toks[i]) > 1) needsSpace = 1;
    }

    text[0] = '\0';
    for (int i = 0; i < postN; i++) {
        if (i > 0 && needsSpace) strcat(text, " ");
        strcat(text, toks[i]);
    }
}

/* 
============================================================
 TASK 2: Convert prefix expression into a binary parse tree
============================================================
Reads prefix tokens left to right to build the parse tree
Operators get child nodes, with '~' using only the right child

*/

Node *buildTree(Token toks[], int n) {
    if (pos >= n) {
        invalidFormula("prefix expression ends too early");
    }

    const char *tok = toks[pos++];
    char c = tok[0];

    if (c == '~' && tok[1] == '\0') {
        Node *node = newNode('~', "", NULL, NULL);
        node->right = buildTree(toks, n);
        return node;
    }
    if ((c == '+' || c == '*' || c == '>') && tok[1] == '\0') {
        Node *node = newNode(c, "", NULL, NULL);
        node->left = buildTree(toks, n);
        node->right = buildTree(toks, n);
        return node;
    }
    if (isalpha((unsigned char) c) || c == '_') {
        return newNode(ATOM, tok, NULL, NULL);           
    }

    invalidFormula("unexpected token in prefix expression");
    return NULL; // Unreachable
}

// Builds a parse tree from a prefix expression
Node *prefixToTree(Token toks[], int n) {
    pos = 0;
    Node *root = buildTree(toks, n);
    if (pos != n) invalidFormula("extra tokens after prefix expression");
    return root;
}



/*============================================================
  TASK 3: Traversals (recursive and iterative)
  ============================================================
 */

// Stores a node and its traversal state in a stack for iterative inorder traversal
 typedef struct {
    Node *node;     /**< the tree node */
    int visited;    /**< how much of this node is already printed (0, 1 or 2) */
} StackItem;

/*
 Prints the tree in inorder using recursion, with parentheses around each subtree
 Parameter used here is "root" which shows the node of the subtree to start from,
 and the base case of recursion to end will be if the node is null
 */

void inorderRecursive(Node *root) {
    if (root == NULL) return;

    if (!isOperator(root->symbol)) {
        showNode(root);
    }
    else if (root->symbol == '~') {
        showStr("~");
        inorderRecursive(root->right);
    }
    else {
        showStr("(");
        inorderRecursive(root->left);
        showNode(root);
        inorderRecursive(root->right);
        showStr(")");
    }
}

/*
 Traverses the tree in inorder using a stack instead of recursion
 The parameter "root" points to the node where the traversal starts
 Each stack entry keeps track of which part of the node has been processed:
 0 means print "(" and go left, 
 1 means print the operator and go right
 2 means print ")" and move to the next node
 The traversal ends when the stack becomes empty
 */

void inorderIterative(Node *root) {
    if (root == NULL) return;

    StackItem *stack = (StackItem *) malloc(sizeof(StackItem) * ((size_t) treeSize + 1));
    int top = -1;

    stack[++top].node = root;
    stack[top].visited = 0;

    while (top >= 0) {
        track(top + 1);
        Node *node = stack[top].node;

        if (!isOperator(node->symbol)) {
            showNode(node);
            top--;
            continue;
        }

        if (node->symbol == '~') {
            if (stack[top].visited == 0) {
                showStr("~");
                stack[top].visited = 1;
                stack[++top].node = node->right;
                stack[top].visited = 0;
            } else {
                top--;
            }
            continue;
        }

        if (stack[top].visited == 0) {
            showStr("(");
            stack[top].visited = 1;
            stack[++top].node = node->left;
            stack[top].visited = 0;
        }
        else if (stack[top].visited == 1) {
            showNode(node);
            stack[top].visited = 2;
            stack[++top].node = node->right;
            stack[top].visited = 0;
        }
        else {
            showStr(")");
            top--;
        }
    }
    free(stack);
}

/*
 Prints the tree in preorder using recursion, visiting the node first,
 then the left subtree and then the right subtree at last
 The parameter "root" points to the node of the subtree to start from
 The recursion ends when the node is null
 */

void preorderRecursive(Node *root) {
    if (root == NULL) return;
    showNode(root);
    showStr(" ");
    preorderRecursive(root->left);
    preorderRecursive(root->right);
}

/*
 Prints the tree in preorder using a stack instead of recursion
 The parameter "root" points to the node of the tree to start from
 The stack keeps track of which nodes still need to be visited
 The traversal ends when the stack becomes empty
 */

void preorderIterative(Node *root) {
    if (root == NULL) return;

    Node **stack = (Node **) malloc(sizeof(Node *) * ((size_t) treeSize + 1));
    int top = -1;
    stack[++top] = root;

    while (top >= 0) {
        track(top + 1);
        Node *node = stack[top--];
        showNode(node);
        showStr(" ");

        /* push right first so left is popped (and printed) first */
        if (node->right != NULL) stack[++top] = node->right;
        if (node->left  != NULL) stack[++top] = node->left;
    }
    free(stack);
}

/*
 Prints the tree in postorder using recursion, visiting the left subtree,
 then the right subtree and finally the current node
 The parameter "root" points to the node of the subtree to start from
 The recursion ends when the node is null
 */

void postorderRecursive(Node *root) {
    if (root == NULL) return;
    postorderRecursive(root->left);
    postorderRecursive(root->right);
    showNode(root);
    showStr(" ");
}

/*
 Prints the tree in postorder using two stacks instead of recursion
 The parameter "root" points to the node of the tree to start from
 The first stack visits the nodes in node, right, left order and the
 second stack reverses this order to print left, right, node
 The traversal ends when the first stack becomes empty
 */

void postorderIterative(Node *root) {
    if (root == NULL) return;

    Node **stack1 = (Node **) malloc(sizeof(Node *) * ((size_t) treeSize + 1));
    Node **stack2 = (Node **) malloc(sizeof(Node *) * ((size_t) treeSize + 1));
    int top1 = -1, top2 = -1;

    stack1[++top1] = root;

    while (top1 >= 0) {
        track(top1 + 1);
        Node *node = stack1[top1--];
        stack2[++top2] = node;
        track(top2 + 1);

        if (node->left  != NULL) stack1[++top1] = node->left;
        if (node->right != NULL) stack1[++top1] = node->right;
    }

    while (top2 >= 0) {
        showNode(stack2[top2--]);
        showStr(" ");
    }
    free(stack1);
    free(stack2);
}

/* 
============================================================
TASK 4: Height of the parse tree
============================================================
 
 1)Height = number of edges on the longest path from the root to a leaf.
 2)An empty tree has height -1, a single node has height 0.

 */

/*
 Finds the height of the tree using recursion.
 The parameter "root" points to the node of the subtree to start from.
 The function returns the height in edges of the longest path from the
 root to a leaf. An empty tree has height -1.
 */

int heightRecursive(Node *root) {
    if (root == NULL) return -1;

    int leftHeight = heightRecursive(root->left);
    int rightHeight = heightRecursive(root->right);

    return 1 + (leftHeight > rightHeight ? leftHeight : rightHeight);
}

/*
 Finds the height of the tree using level-order traversal with a queue.
 The parameter "root" points to the node of the tree to start from.
 The queue is used to visit nodes level by level, and each pass of the
 loop handles one full level.
 The function returns the height in edges, which is the number of levels
 minus 1. An empty tree has height -1.
 */
 
int heightIterative(Node *root) {
    if (root == NULL) return -1;

    Node **queue = (Node **) malloc(sizeof(Node *) * ((size_t) treeSize + 1));
    int front = 0, rear = 0;
    queue[rear++] = root;

    int levels = 0;

    while (front < rear) {
        int levelSize = rear - front;
        track(levelSize);
        levels++;

        for (int i = 0; i < levelSize; i++) {
            Node *node = queue[front++];
            if (node->left  != NULL) queue[rear++] = node->left;
            if (node->right != NULL) queue[rear++] = node->right;
        }
    }
    free(queue);
    return levels - 1;
}

/*
 ============================================================
 TASK 5: Evaluate the formula and print the truth table
 ============================================================
 */

// Collects distinct variables and assigns each leaf its variable index
void collectVariables(Node *root) {
    if (root == NULL) return;

    if (!isOperator(root->symbol)) {
        for (int i = 0; i < varCount; i++) {
            if (strcmp(varNames[i], root->name) == 0) {
                root->var = i;
                return;
            }
        }
        strcpy(varNames[varCount], root->name);
        root->var = varCount++;
        return;
    }

    collectVariables(root->left);
    collectVariables(root->right);
}

// Evaluates the tree using the current variable values and returns 0 or 1
int evaluate(Node *root) {
    if (!isOperator(root->symbol)) {
        return varValues[root->var];
    }

    if (root->symbol == '~') {
        return !evaluate(root->right);
    }

    int left = evaluate(root->left);
    int right = evaluate(root->right);

    if (root->symbol == '+') return left || right;
    if (root->symbol == '*') return left && right;
    if (root->symbol == '>') return (!left) || right;

    return 0; /* unreachable */
}

// Tests all truth assignments and counts how many make the formula true
// Skips the full table if there are too many variables

long truthTable(Node *root, int print) {
    if (varCount > TT_LIMIT) {
        for (int i = 0; i < varCount; i++) varValues[i] = 0;
        evaluate(root);
        return -1;
    }

    if (print) {
        for (int i = 0; i < varCount; i++) printf("%-6s", varNames[i]);
        printf("| Result\n");
        for (int i = 0; i < varCount; i++) printf("------");
        printf("|-------\n");
    }

    long rows = 1L << varCount;   //2^varCount 
    long trueRows = 0;

    for (long mask = 0; mask < rows; mask++) {
        for (int i = 0; i < varCount; i++) {
            //leftmost variable toggles slowest, like a textbook table 
            varValues[i] = (int) ((mask >> (varCount - 1 - i)) & 1);
            if (print) printf("%-6c", varValues[i] ? 'T' : 'F');
        }
        int result = evaluate(root);
        if (print) printf("| %c\n", result ? 'T' : 'F');
        trueRows += result;
    }
    return trueRows;
}

/* 
============================================================
  DIMACS CNF reader (SAT competition benchmark files)
============================================================
 Reads DIMACS CNF files used for SAT problems

 Adds a node to a dynamically growing array
 */
Node **pushNode(Node **arr, int *count, int *cap, Node *n) {
    if (*count == *cap) {
        *cap = (*cap == 0) ? 64 : *cap * 2;
        arr = (Node **) realloc(arr, sizeof(Node *) * (size_t) (*cap));
        if (arr == NULL) {
            fprintf(stderr, "Error: out of memory\n");
            exit(1);
        }
    }
    arr[(*count)++] = n;
    return arr;
}

// Combines subtrees into a balanced tree using the given operator

Node *buildBalanced(Node **arr, int lo, int hi, char op) {
    if (hi - lo == 1) return arr[lo];
    int mid = (lo + hi) / 2;
    return newNode(op, "", buildBalanced(arr, lo, mid, op),
                           buildBalanced(arr, mid, hi, op));
}

// Reads a DIMACS CNF file and builds its parse tree
Node *readCnf(const char *path) {
    FILE *f = fopen(path, "r");
    if (f == NULL) {
        fprintf(stderr, "Error: cannot open '%s'\n", path);
        exit(1);
    }

    char line[4096];
    int V = 0, C = 0, found = 0;
    while (fgets(line, sizeof(line), f) != NULL) {
        if (line[0] == 'p') {
            if (sscanf(line, "p cnf %d %d", &V, &C) != 2) break;
            found = 1;
            break;
        }
    }
    if (!found || V <= 0 || V > MAXVARS) {
        fprintf(stderr, "Error: missing/invalid 'p cnf V C' header (V must be 1..%d)\n", MAXVARS);
        exit(1);
    }
    cnfClauses = C;

    Node **lits = NULL, **clauses = NULL;
    int litCount = 0, litCap = 0, clauseCount = 0, clauseCap = 0;

    while (fgets(line, sizeof(line), f) != NULL) {
        char *s = line;
        while (isspace((unsigned char) *s)) s++;
        if (*s == '\0' || *s == 'c') continue;
        if (*s == '%') break;                   

        while (*s != '\0') {
            while (isspace((unsigned char) *s)) s++;
            if (*s == '\0') break;

            char *end = NULL;
            long lit = strtol(s, &end, 10);
            if (end == s) break;                 
            s = end;

            if (lit != 0) {
                if (lit > V || lit < -V) {
                    fprintf(stderr, "Error: literal %ld is outside the declared %d variables\n",
                            lit, V);
                    exit(1);
                }
                int v = (int) (lit < 0 ? -lit : lit);
                char nm[NAMELEN];
                snprintf(nm, sizeof(nm), "x%d", v);
                Node *atom = newNode(ATOM, nm, NULL, NULL);
                atom->var = v - 1;
                Node *leaf = (lit < 0) ? newNode('~', "", NULL, atom) : atom;
                lits = pushNode(lits, &litCount, &litCap, leaf);
            } else {
                if (litCount == 0) {
                    fprintf(stderr, "Error: empty clause found (not supported)\n");
                    exit(1);
                }
                clauses = pushNode(clauses, &clauseCount, &clauseCap,
                                   buildBalanced(lits, 0, litCount, '+'));
                litCount = 0;
            }
        }
    }
    fclose(f);

    if (litCount > 0) {                        
        clauses = pushNode(clauses, &clauseCount, &clauseCap,
                           buildBalanced(lits, 0, litCount, '+'));
    }
    if (clauseCount == 0) {
        fprintf(stderr, "Error: no clauses found\n");
        exit(1);
    }
    if (clauseCount != C) {
        printf("Warning: header says %d clauses but %d were read\n", C, clauseCount);
    }

    Node *root = buildBalanced(clauses, 0, clauseCount, '*');
    free(lits);
    free(clauses);

    varCount = V;
    for (int i = 0; i < V; i++) snprintf(varNames[i], NAMELEN, "x%d", i + 1);
    return root;
}

/* 
============================================================
  TASK 6: Analysis of output, efficiency and memory
============================================================
 Every algorithm is run silently and timed with clock(). Very fast algorithms are repeated many times and the average is reported.
 "Extra memory" is the largest size reached by the explicit stack/queue (iterative versions) or the recursion depth (recursive versions).
 */

// Stores one row of the analysis results.
typedef struct {
    const char *task;      // Task name
    const char *method;    // Method used
    const char *timeC;     // Time complexity
    const char *spaceC;    // Space complexity
    double micros;         // Execution time in microseconds
    char aux[64];          // Extra memory usage
} Result;

Result results[32];        // Stores the results
int resultCount = 0;       // Number of rows added

// Adds a row to the results table.
void addResult(const char *task, const char *method, const char *tc,
               const char *sc, double micros, const char *aux) {
    Result *r = &results[resultCount++];
    r->task = task;
    r->method = method;
    r->timeC = tc;
    r->spaceC = sc;
    r->micros = micros;
    snprintf(r->aux, sizeof(r->aux), "%s", aux);
}

/**
 * @brief Times a function and stores the result.
 *
 * Runs fn() once; if it was very fast it is repeated (up to 100000 times)
 * so that the average is meaningful.
 *
 * @param task     task name
 * @param method   method name
 * @param tc       time complexity text
 * @param sc       space complexity text
 * @param fn       function to time (takes no arguments)
 * @param auxFixed extra memory to report, or -1 to use peakAux
 * @param unit     unit of the extra memory (e.g. "call frames")
 */
void bench(const char *task, const char *method, const char *tc, const char *sc,
           void (*fn)(void), long auxFixed, const char *unit) {
    int savedVerbose = verbose;
    verbose = 0;
    peakAux = 0;

    clock_t start = clock();
    fn();
    double t = (double) (clock() - start) / CLOCKS_PER_SEC;

    if (t < 0.05) {
        int reps = (int) (0.05 / (t > 1e-7 ? t : 1e-7));
        if (reps > 100000) reps = 100000;
        if (reps > 1) {
            start = clock();
            for (int i = 0; i < reps; i++) fn();
            t = (double) (clock() - start) / CLOCKS_PER_SEC / reps;
        }
    }
    verbose = savedVerbose;

    char aux[64];
    snprintf(aux, sizeof(aux), "%ld %s", auxFixed >= 0 ? auxFixed : (long) peakAux, unit);
    addResult(task, method, tc, sc, t * 1e6, aux);
}

/* small wrappers so that every algorithm can be timed through bench() */
void runT1(void)      { Token toks[MAXTOK]; int n; char text[MAXPREFIX];
                        infixToPrefix(gInfix, toks, &n, text); }
void runT2(void)      { Node *t = prefixToTree(gPrefixToks, gPrefixCount); freeTree(t); }
void runInRec(void)   { inorderRecursive(gRoot); }
void runInIter(void)  { inorderIterative(gRoot); }
void runPreRec(void)  { preorderRecursive(gRoot); }
void runPreIter(void) { preorderIterative(gRoot); }
void runPostRec(void) { postorderRecursive(gRoot); }
void runPostIter(void){ postorderIterative(gRoot); }
void runHRec(void)    { heightRecursive(gRoot); }
void runHIter(void)   { heightIterative(gRoot); }
void runEval(void)    { evaluate(gRoot); }
void runTruth(void)   { truthTable(gRoot, 0); }

/**
 * @brief Times every algorithm on the current tree (gRoot).
 * @param infixMode 1 if Tasks 1 and 2 should be timed too
 */
void runAnalysis(int infixMode) {
    long depth = treeHeight + 1;   /* recursion depth = height + 1 frames */

    if (infixMode) {
        bench("Task 1 infix to prefix", "stack (reverse+swap)", "O(L)", "O(L)",
              runT1, (long) strlen(gInfix), "chars");
        bench("Task 2 prefix to tree", "recursive", "O(n)", "O(h) + tree",
              runT2, depth, "call frames");
    }
    bench("Task 3 inorder",   "recursive", "O(n)", "O(h)", runInRec,    depth, "call frames");
    bench("Task 3 inorder",   "iterative", "O(n)", "O(h)", runInIter,   -1, "stack entries");
    bench("Task 3 preorder",  "recursive", "O(n)", "O(h)", runPreRec,   depth, "call frames");
    bench("Task 3 preorder",  "iterative", "O(n)", "O(h)", runPreIter,  -1, "stack entries");
    bench("Task 3 postorder", "recursive", "O(n)", "O(h)", runPostRec,  depth, "call frames");
    bench("Task 3 postorder", "iterative (2 stacks)", "O(n)", "O(n)", runPostIter, -1, "stack entries");
    bench("Task 4 height",    "recursive", "O(n)", "O(h)", runHRec,     depth, "call frames");
    bench("Task 4 height",    "iterative (BFS)", "O(n)", "O(w)", runHIter, -1, "queue entries");
    bench("Task 5 evaluate",  "one assignment", "O(n)", "O(h)", runEval, depth, "call frames");
    bench("Task 5 truth table", "all 2^v rows", "O(2^v * n)", "O(v + h)", runTruth,
          depth, "call frames");
}

/** @brief Prints the Task 6 results table on the screen. */
void printAnalysis(void) {
    printf("\n=========== TASK 6: ANALYSIS ===========\n");
    printf("Tree nodes n = %d, height h = %d, variables v = %d\n", treeSize, treeHeight, varCount);
    printf("Memory of the tree itself: %d nodes x %zu bytes = %.1f KB\n",
           treeSize, sizeof(Node), (size_t) treeSize * sizeof(Node) / 1024.0);
    if (gTrueRows >= 0) printf("Truth table: %ld of %ld rows are true\n", gTrueRows, 1L << varCount);
    else printf("Truth table skipped (more than %d variables); one evaluation was done instead\n", TT_LIMIT);

    printf("\n%-22s %-22s %-11s %-9s %12s  %s\n",
           "Task", "Method", "Time", "Space", "Time (us)", "Measured extra memory");
    for (int i = 0; i < resultCount; i++) {
        Result *r = &results[i];
        printf("%-22s %-22s %-11s %-9s %12.3f  %s\n",
               r->task, r->method, r->timeC, r->spaceC, r->micros, r->aux);
    }
    printf("(n = nodes, h = height, w = widest level, L = input length, v = variables)\n");
}

/** @brief Writes text to an HTML file, escaping < > and &. */
void htmlEscape(FILE *f, const char *s) {
    for (; *s; s++) {
        if (*s == '<') fputs("&lt;", f);
        else if (*s == '>') fputs("&gt;", f);
        else if (*s == '&') fputs("&amp;", f);
        else fputc(*s, f);
    }
}

/**
 * @brief Saves the analysis as a styled HTML page (analysis_report.html).
 * @param input description of the input (formula text or file name)
 */
void writeHtmlReport(const char *input) {
    FILE *f = fopen("analysis_report.html", "w");
    if (f == NULL) {
        printf("Could not write analysis_report.html\n");
        return;
    }
    fputs("<!DOCTYPE html><html lang=\"en\"><head><meta charset=\"utf-8\">"
          "<title>Assignment 1 - Analysis</title><style>"
          "body{font-family:Segoe UI,Arial,sans-serif;background:#f4f6fb;color:#1f2937;margin:0}"
          "header{background:linear-gradient(135deg,#1e3a8a,#3b82f6);color:#fff;padding:32px 48px}"
          "header h1{margin:0 0 6px 0;font-size:28px}header p{margin:0;opacity:.9}"
          "main{max-width:1100px;margin:28px auto;padding:0 24px}"
          ".cards{display:grid;grid-template-columns:repeat(auto-fit,minmax(170px,1fr));gap:14px}"
          ".card{background:#fff;border-radius:12px;padding:16px;box-shadow:0 2px 8px rgba(0,0,0,.08)}"
          ".card b{display:block;font-size:24px;color:#1e40af}.card span{color:#6b7280;font-size:13px}"
          "h2{margin-top:34px;color:#1e3a8a}"
          "table{width:100%;border-collapse:collapse;background:#fff;border-radius:12px;"
          "overflow:hidden;box-shadow:0 2px 8px rgba(0,0,0,.08)}"
          "th{background:#1e40af;color:#fff;text-align:left;padding:10px 12px;font-size:14px}"
          "td{padding:9px 12px;border-bottom:1px solid #e5e7eb;font-size:14px}"
          "tr:nth-child(even) td{background:#f8fafc}td.num{text-align:right;font-family:Consolas,monospace}"
          "code{background:#e0e7ff;padding:2px 6px;border-radius:4px}"
          "ul{line-height:1.7}footer{text-align:center;color:#6b7280;margin:40px 0;font-size:13px}"
          "</style></head><body>", f);

    fputs("<header><h1>CS F214 Logic in CS &ndash; Assignment 1 (Part A)</h1>"
          "<p>Analysis of output, efficiency and memory usage</p></header><main>", f);

    fputs("<h2>Input</h2><p><code>", f);
    htmlEscape(f, input);
    fputs("</code></p><div class=\"cards\">", f);
    fprintf(f, "<div class=\"card\"><b>%d</b><span>tree nodes (n)</span></div>", treeSize);
    fprintf(f, "<div class=\"card\"><b>%d</b><span>tree height (h)</span></div>", treeHeight);
    fprintf(f, "<div class=\"card\"><b>%d</b><span>variables (v)</span></div>", varCount);
    fprintf(f, "<div class=\"card\"><b>%.1f KB</b><span>memory of the tree (%d nodes x %zu bytes)</span></div>",
            (size_t) treeSize * sizeof(Node) / 1024.0, treeSize, sizeof(Node));
    if (gTrueRows >= 0)
        fprintf(f, "<div class=\"card\"><b>%ld / %ld</b><span>truth table rows that are true</span></div>",
                gTrueRows, 1L << varCount);
    else
        fprintf(f, "<div class=\"card\"><b>skipped</b><span>more than %d variables</span></div>", TT_LIMIT);
    fputs("</div>", f);

    fputs("<h2>Measured results</h2><table><tr><th>Task</th><th>Method</th><th>Time</th>"
          "<th>Space</th><th>Time per run (&micro;s)</th><th>Measured extra memory</th></tr>", f);
    for (int i = 0; i < resultCount; i++) {
        Result *r = &results[i];
        fprintf(f, "<tr><td>%s</td><td>%s</td><td>%s</td><td>%s</td><td class=\"num\">%.3f</td><td>%s</td></tr>",
                r->task, r->method, r->timeC, r->spaceC, r->micros, r->aux);
    }
    fputs("</table><p>n = nodes, h = height, w = widest level, L = input length, v = variables.</p>", f);

    fputs("<h2>Observations</h2><ul>"
          "<li>Every traversal and both height algorithms visit each node once, so they take O(n) time.</li>"
          "<li>Recursive versions use the call stack: depth h + 1. Iterative versions use an explicit stack "
          "or queue instead, which is why overflow of the call stack is avoided.</li>"
          "<li>Iterative postorder with two stacks needs O(n) extra memory; the other traversals need only O(h).</li>"
          "<li>Iterative height (BFS) needs memory for the widest level of the tree.</li>"
          "<li>For CNF files the clauses and the literals inside each clause are joined into <b>balanced</b> "
          "trees, so h is about log<sub>2</sub> n and recursion stays shallow.</li>"
          "<li>The truth table has 2<sup>v</sup> rows and each row costs one evaluation of O(n), so it is only "
          "produced for up to 16 variables.</li></ul>", f);

    fputs("</main><footer>Generated by logic_assignment.c</footer></body></html>", f);
    fclose(f);
    printf("\nAnalysis page saved as analysis_report.html\n");
}

/* 
============================================================
 Printing the results of Tasks 3 to 5
============================================================
 */

// Prints the outputs of Tasks 3, 4 and 5 for the current tree
void showAllTasks(Node *root) {
    verbose = 1;

    /* ---------- Task 3 ---------- */
    printf("\nInorder (recursive)   : ");
    inorderRecursive(root);
    printf("\nInorder (iterative)   : ");
    inorderIterative(root);

    printf("\n\nPreorder (recursive)  : ");
    preorderRecursive(root);
    printf("\nPreorder (iterative)  : ");
    preorderIterative(root);

    printf("\n\nPostorder (recursive) : ");
    postorderRecursive(root);
    printf("\nPostorder (iterative) : ");
    postorderIterative(root);

    /* ---------- Task 4 ---------- */
    printf("\n\nHeight (recursive)    : %d\n", heightRecursive(root));
    printf("Height (iterative)    : %d\n", heightIterative(root));

    /* ---------- Task 5 ---------- */
    printf("\nDistinct atoms        : %d\n", varCount);
    printf("\nTruth table:\n");
    gTrueRows = truthTable(root, 1);
}

//Sets up size/height info that the other functions rely on
void prepareTree(Node *root) {
    gRoot = root;
    treeSize = countNodes(root);
    treeHeight = heightRecursive(root);
}

/* 
============================================================
 main
============================================================
 */

int runInfixMode(void) {
    printf("CS F214 Logic in CS - Assignment 1 (Part A)\n");
    printf("Operators: ~ NOT, + OR, * AND, > IMPLICATION\n");
    printf("Enter a fully parenthesized infix formula (e.g. ((P*Q)>~R)):\n");
    if (fgets(gInfix, MAX, stdin) == NULL) {
        fprintf(stderr, "Error: no formula entered\n");
        return 1;
    }
    gInfix[strcspn(gInfix, "\r\n")] = '\0';   /* drop the trailing newline */

    /* ---------- Task 1 ---------- */
    infixToPrefix(gInfix, gPrefixToks, &gPrefixCount, gPrefix);
    printf("\nPrefix expression: %s\n", gPrefix);

    /* ---------- Task 2 ---------- */
    Node *root = prefixToTree(gPrefixToks, gPrefixCount);
    prepareTree(root);
    collectVariables(root);

    /* ---------- Tasks 3, 4, 5 ---------- */
    showAllTasks(root);

    /* ---------- Task 6 ---------- */
    runAnalysis(1);
    printAnalysis();
    writeHtmlReport(gInfix);

    freeTree(root);
    return 0;
}

/*
  CNF mode: Tasks 3 to 6 on a DIMACS benchmark file.
  path path of the .cnf file
  @return exit code
 */
int runCnfMode(const char *path) {
    printf("CS F214 Logic in CS - Assignment 1 (Part A)\n");
    printf("Input mode: DIMACS CNF file '%s'\n", path);
    printf("(clauses are joined by AND, literals inside a clause by OR;\n");
    printf(" Tasks 1 and 2 are for infix input, so the CNF is turned into a tree directly)\n");

    clock_t start = clock();
    Node *root = readCnf(path);
    double loadMicros = (double) (clock() - start) / CLOCKS_PER_SEC * 1e6;
    prepareTree(root);

    printf("\nDIMACS header: %d variables, %d clauses\n", varCount, cnfClauses);
    printf("Variables: %d, tree nodes: %d, tree height: %d\n", varCount, treeSize, treeHeight);

    if (treeSize <= SMALL_TREE) {
        showAllTasks(root);
    } else {
        printf("\nThe tree has %d nodes, so the traversal printouts are skipped (they would be huge).\n",
               treeSize);
        int heightRec = heightRecursive(root);
        int heightIter = heightIterative(root);
        printf("Height (recursive)    : %d\n", heightRec);
        printf("Height (iterative)    : %d\n", heightIter);
        printf("Both heights agree: %s\n", heightRec == heightIter ? "yes" : "NO");
        gTrueRows = truthTable(root, 0);
        if (gTrueRows >= 0)
            printf("Truth table: %ld of %ld rows are true (printing skipped, tree is large)\n",
                   gTrueRows, 1L << varCount);
        else
            printf("Truth table skipped: %d variables is more than %d.\n", varCount, TT_LIMIT);
    }

    /* ---------- Task 6 ---------- */
    char aux[64];
    snprintf(aux, sizeof(aux), "%.1f KB tree", (size_t) treeSize * sizeof(Node) / 1024.0);
    addResult("Read CNF into tree", "balanced build", "O(L)", "O(L)", loadMicros, aux);
    runAnalysis(0);
    printAnalysis();
    writeHtmlReport(path);

    freeTree(root);
    return 0;
}

// Runs the program in formula input or DIMACS file mode.
int main(int argc, char **argv) {
    if (argc >= 3 && strcmp(argv[1], "--dimacs") == 0) return runCnfMode(argv[2]);
    if (argc >= 2 && strcmp(argv[1], "--dimacs") != 0) return runCnfMode(argv[1]);
    if (argc >= 2) {
        fprintf(stderr, "Usage: %s [--dimacs] file.cnf\n", argv[0]);
        return 1;
    }
    return runInfixMode();
}