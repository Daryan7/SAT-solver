#include <iostream>
#include <stdlib.h>
#include <algorithm>
#include <vector>
#include <list>
#include <sys/time.h>
using namespace std;

typedef unsigned int uint;

#define UNDEF -1
#define TRUE 1
#define FALSE 0

struct Appearings {
    uint var, appearings;
};

uint numVars;
uint numClauses;
vector<vector<int>> clauses;
vector<vector<uint>> varRefsTrue;
vector<vector<uint>> varRefsFalse;
vector<Appearings> varApp;
vector<int> model;
vector<int> modelStack;
uint indexOfNextLitToPropagate;
uint decisionLevel;

bool compare(Appearings left, Appearings right) {
    //if (left.appearings == right.appearings) return varRefsFalse[left.var].size() > varRefsFalse[right.var].size();
    return left.appearings > right.appearings;
}

void readClauses() {
    // Skip comments
    char c = cin.get();
    while (c == 'c') {
        while (c != '\n') c = cin.get();
        c = cin.get();
    }
    // Read "cnf numVars numClauses"
    string aux;
    cin >> aux >> numVars >> numClauses;
    clauses.resize(numClauses);
    varRefsTrue = vector<vector<uint>>(numVars+1);
    varRefsFalse = vector<vector<uint>>(numVars+1);
    varApp = vector<Appearings>(numVars);

    for (uint i = 0; i < numVars; ++i) {
        varApp[i].var = i+1;
        varApp[i].appearings = 0;
    }
    // Read clauses
    for (uint i = 0; i < numClauses; ++i) {
        int lit;
        while (cin >> lit and lit != 0) {
            clauses[i].push_back(lit);
            if (lit > 0) {
                varRefsTrue[lit].push_back(i);
                varApp[lit-1].appearings++;
            }
            else {
                varRefsFalse[-lit].push_back(i);
                varApp[-lit-1].appearings++;
            }
        }
    }

    sort(varApp.begin(), varApp.end(), compare);
    //for (Appearings x : varApp) cout << x.lit << " " << x.appearings << endl;
}

int currentValueInModel(int lit) {
    return lit >= 0 ? model[lit] : (model[-lit] == UNDEF ? UNDEF : 1-model[-lit]);
}

void setLiteralToTrue(int lit) {
    modelStack.push_back(lit);
    if (lit > 0) model[lit] = TRUE;
    else model[-lit] = FALSE;
}

bool propagateGivesConflict() {
    while (indexOfNextLitToPropagate < modelStack.size()) {
        int litToPropagate = modelStack[indexOfNextLitToPropagate];
        ++indexOfNextLitToPropagate;

        uint* vec;
        uint size;
        if (litToPropagate > 0) {
            vec = &varRefsFalse[litToPropagate][0];
            size = varRefsFalse[litToPropagate].size();
        }
        else {
            vec = &varRefsTrue[-litToPropagate][0];
            size = varRefsTrue[-litToPropagate].size();
        }

        for (uint i = 0; i < size; ++i) {
            bool someLitTrue = false;
            int numUndefs = 0;
            int lastLitUndef = 0;
            int clause = vec[i];
            for (uint k = 0; not someLitTrue and k < clauses[clause].size(); ++k) {
                int val = currentValueInModel(clauses[clause][k]);
                if (val == TRUE) someLitTrue = true;
                else if (val == UNDEF) {++numUndefs;lastLitUndef = clauses[clause][k];}
            }
            if (not someLitTrue and numUndefs == 0) return true; // conflict! all lits false
            else if (not someLitTrue and numUndefs == 1) setLiteralToTrue(lastLitUndef);
        }
    }
    return false;
}

void backtrack() {
    uint i = modelStack.size() - 1;
    int lit = 0;
    while (modelStack[i] != 0) { // 0 is the DL mark
        lit = modelStack[i];
        model[abs(lit)] = UNDEF;
        modelStack.pop_back();
        --i;
    }
    // at this point, lit is the last decision
    modelStack.pop_back(); // remove the DL mark
    --decisionLevel;
    indexOfNextLitToPropagate = modelStack.size();
    setLiteralToTrue(-lit);  // reverse last decision
}

// Heuristic for finding the next decision literal:
int getNextDecisionLiteral() {
    for (uint i = 0; i < numVars; ++i) {
        uint var = varApp[i].var;
        if (model[var] == UNDEF) //return var;
            return varRefsTrue[var].size() > varRefsFalse[var].size() ? -var : var;
    }
    return 0; // reurns 0 when all literals are defined
}

void checkmodel() {
    for (uint i = 0; i < numClauses; ++i) {
        bool someTrue = false;
        for (uint j = 0; not someTrue and j < clauses[i].size(); ++j)
            someTrue = (currentValueInModel(clauses[i][j]) == TRUE);
        if (not someTrue) {
            cerr << "Error in model, clause is not satisfied:";
            for (uint j = 0; j < clauses[i].size(); ++j) cerr << clauses[i][j] << " ";
            cerr << endl;
            exit(1);
        }
    }
}

int main() {
    readClauses(); // reads numVars, numClauses and clauses
    model.resize(numVars+1, UNDEF);
    indexOfNextLitToPropagate = 0;
    decisionLevel = 0;

    timeval start, end;

    gettimeofday(&start, NULL);

    // Take care of initial unit clauses, if any
    for (uint i = 0; i < numClauses; ++i)
        if (clauses[i].size() == 1) {
            int lit = clauses[i][0];
            int val = currentValueInModel(lit);
            if (val == FALSE) {
                cout << "UNSATISFIABLE" << endl;
                gettimeofday(&end, NULL);
                cout << (end.tv_sec+((double)end.tv_usec/1000000))-(start.tv_sec+((double)start.tv_usec/1000000)) << endl;
                return 10;
            }
            else if (val == UNDEF) setLiteralToTrue(lit);
        }

    // DPLL algorithm
    while (true) {
        while (propagateGivesConflict()) {
            if (decisionLevel == 0) {
                cout << "UNSATISFIABLE" << endl;
                gettimeofday(&end, NULL);
                cout << (end.tv_sec+((double)end.tv_usec/1000000))-(start.tv_sec+((double)start.tv_usec/1000000)) << endl;
                return 10;
            }
            backtrack();
        }
        int decisionLit = getNextDecisionLiteral();
        if (decisionLit == 0) {
            checkmodel(); cout << "SATISFIABLE" << endl;
            gettimeofday(&end, NULL);
            cout << (end.tv_sec+((double)end.tv_usec/1000000))-(start.tv_sec+((double)start.tv_usec/1000000)) << endl;
            return 20;
        }
        // start new decision level:
        modelStack.push_back(0);  // push mark indicating new DL
        ++indexOfNextLitToPropagate;
        ++decisionLevel;
        setLiteralToTrue(decisionLit);    // now push decisionLit on top of the mark
    }
}  
