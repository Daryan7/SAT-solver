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

uint numVars;
uint numClauses;
vector<vector<int>> clauses;
vector<vector<uint>> varRefsTrue;
vector<vector<uint>> varRefsFalse;
vector<uint> varApp;
vector<vector<int>> propagMotive;
vector<int> model;
vector<int> modelStack;
uint indexOfNextLitToPropagate;
uint decisionLevel;

bool compare(uint left, uint right) {
    uint appLeft = varRefsFalse[left].size()+varRefsTrue[left].size();
    uint appRight = varRefsFalse[right].size()+varRefsTrue[right].size();
    if (appLeft == appRight) return varRefsFalse[left].size() > varRefsFalse[right].size();
    return appLeft > appRight;
}

bool compare3(int left, int right) {
    return abs(left) < abs(right);
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
    varApp = vector<uint>(numVars);

    for (uint i = 0; i < numVars; ++i) {
        varApp[i] = i+1;
    }
    // Read clauses
    for (uint i = 0; i < numClauses; ++i) {
        int lit;
        while (cin >> lit and lit != 0) {
            clauses[i].push_back(lit);
            if (lit > 0) {
                varRefsTrue[lit].push_back(i);
            }
            else {
                varRefsFalse[-lit].push_back(i);
            }
        }
        sort(clauses[i].begin(), clauses[i].end(), compare3);
    }

    sort(varApp.begin(), varApp.end(), compare);
}

int currentValueInModel(int lit) {
    return lit >= 0 ? model[lit] : (model[-lit] == UNDEF ? UNDEF : 1-model[-lit]);
}

void setLiteralToTrue(int lit) {
    modelStack.push_back(lit);
    if (lit > 0) model[lit] = TRUE;
    else model[-lit] = FALSE;
}

bool propagateGivesConflict(uint& cause) {
    while (indexOfNextLitToPropagate < modelStack.size()) {
        int litToPropagate = modelStack[indexOfNextLitToPropagate];
#ifdef DEBUG
        cout << "Propagating " << litToPropagate << endl;
#endif
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
            uint clause = *vec;
            ++vec;
            for (uint k = 0; not someLitTrue and k < clauses[clause].size(); ++k) {
                int val = currentValueInModel(clauses[clause][k]);
                if (val == TRUE) someLitTrue = true;
                else if (val == UNDEF) {++numUndefs;lastLitUndef = clauses[clause][k];}
            }
            if (not someLitTrue and numUndefs == 0) {
                cause = clause;
                return true; // conflict! all lits false
            }
            else if (not someLitTrue and numUndefs == 1) {
                propagMotive[abs(lastLitUndef)] = clauses[clause];
#ifdef DEBUG
                cout << "Propagated " << lastLitUndef << " " << clause << " " << clauses.size() << endl;
                for (int x : clauses[clause]) cout << x << " ";
                cout << endl;
#endif
                setLiteralToTrue(lastLitUndef);
            }
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

void backjump(uint clauseOfConflict) {
    vector<int> clauseConflict = clauses[clauseOfConflict];
#ifdef DEBUG
    cout << "BackJumping" << endl;
    for (int x : clauseConflict) cout << x << " ";
    cout << endl;
    for (int x : modelStack) cout << x << " ";
    cout << endl << endl;
    uint count = 0;
#endif
    int found = 0;
    uint numFalseLits = 0;
    uint i;
    int lit;
    for (i = modelStack.size()-1, lit = modelStack[i]; lit != 0; --i, lit = modelStack[i]) {
        for (int x : clauseConflict) {
            if (x == -lit) {
                if (not found) found = lit;
                ++numFalseLits;
            }
        }
    }
    while (numFalseLits > 1) {
       // vector<int>& cause = clauses[propagMotive[abs(found)]];
        vector<int>& cause = propagMotive[abs(found)];
#ifdef DEBUG
        for (int x : cause) cout << x << " ";
        cout << endl;
        for (int x : clauseConflict) cout << x << " ";
        cout << endl;
#endif
        vector<int> aux;
        aux.reserve(clauseConflict.size()+cause.size()-1);

        i = 0;
        uint j = 0;
        while (i < clauseConflict.size() and j < cause.size()) {
            uint litLeft = abs(clauseConflict[i]);
            uint litRight = abs(cause[j]);

            if (litLeft < litRight) {
                aux.push_back(clauseConflict[i]);
                ++i;
            }
            else if (litLeft > litRight) {
                aux.push_back(cause[j]);
                ++j;
            }
            else {
                if (clauseConflict[i] == cause[j]) {
                    aux.push_back(cause[j]);
                }
                ++i;++j;
            }
        }
        while (i < clauseConflict.size()) {
           aux.push_back(clauseConflict[i]);
           ++i;
        }
        while (j < cause.size()) {
            aux.push_back(cause[j]);
            ++j;
        }

        found = 0;
        numFalseLits = 0;
        for (uint j = modelStack.size()-1; modelStack[j] != 0; --j) {
            int lit = modelStack[j];
            for (int x : aux) {
                if (x == -lit) {
                    if (not found) found = lit;
                    ++numFalseLits;
                }
            }
        }
#ifdef DEBUG
        cout << "RESULT" << endl;
        for (int x : aux) cout << x << " ";
        cout << endl;
        cout << "Found " << found << " num false lits " << numFalseLits << endl;
        //if (count == 20) exit(-1);
        ++count;
#endif
        clauseConflict = aux;
    }

    clauses.push_back(clauseConflict);
    for (int x : clauseConflict) {
        if (x > 0) varRefsTrue[x].push_back(clauses.size()-1);
        else varRefsFalse[-x].push_back(clauses.size()-1);
    }

    if (clauseConflict.size() == 1) {
        //cout << "Emptying stack" << endl;
        i = modelStack.size()-1;
        while (i > 0) {
            int lit = modelStack[i];
            model[abs(lit)] = UNDEF;
            modelStack.pop_back();
            --i;
        }

        decisionLevel = 1;
        //cout << "Propagating 1 lit clause" << endl;
        // Take care of initial unit clauses, if any
        for (uint j = 0; j < clauses.size(); ++j) {
            if (clauses[j].size() == 1) {
                //cout << j << " Has one lit: " << clauses[j][0];
                int lit = clauses[j][0];
                int val = currentValueInModel(lit);
                if (val == FALSE) {
                    //gettimeofday(&end, NULL);
                   // cout << (end.tv_sec+((double)end.tv_usec/1000000))-(start.tv_sec+((double)start.tv_usec/1000000)) << endl;
                    cout << "UNSATISFIABLE" << endl;
                    exit(10);
                }
                else if (val == UNDEF) setLiteralToTrue(lit);
            }
        }
        indexOfNextLitToPropagate = modelStack.size()-1;
        //cout << "New index " << indexOfNextLitToPropagate << endl;
        return;
    }

    i = modelStack.size()-1;
    bool eq = false;
    bool trigger = false;
    while (not eq) {
        int lit = modelStack[i];
        for (int x : clauseConflict) {
            if (abs(x) == abs(lit) and trigger) {
                eq = true;
            }
        }
        if (not eq) {
            if (lit != 0) model[abs(lit)] = UNDEF;
            else {
                trigger = true;
                --decisionLevel;
            }
            modelStack.pop_back();
            --i;
        }
    }
    //propagMotive[abs(found)] = clauseConflict;
    indexOfNextLitToPropagate = modelStack.size()-1;
    //setLiteralToTrue(-found);
#ifdef DEBUG
    cout << "After back jumping" << endl;
    for (int x : modelStack) cout << x << " ";
    cout << endl;
#endif
}

// Heuristic for finding the next decision literal:
int getNextDecisionLiteral() {
    for (uint i = 0; i < numVars; ++i) {
        uint var = varApp[i];
        if (model[var] == UNDEF) return var;
            //return varRefsTrue[var].size() > varRefsFalse[var].size() ? -var : var;
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
    timeval start, end;
    gettimeofday(&start, NULL);

    readClauses(); // reads numVars, numClauses and clauses
    model.resize(numVars+1, UNDEF);
    propagMotive = vector<vector<int>>(numVars+1);
    indexOfNextLitToPropagate = 0;
    decisionLevel = 0;

    // Take care of initial unit clauses, if any
    for (uint i = 0; i < numClauses; ++i)
        if (clauses[i].size() == 1) {
            int lit = clauses[i][0];
            int val = currentValueInModel(lit);
            if (val == FALSE) {
                gettimeofday(&end, NULL);
                cout << (end.tv_sec+((double)end.tv_usec/1000000))-(start.tv_sec+((double)start.tv_usec/1000000)) << endl;
                cout << "UNSATISFIABLE" << endl;
                return 10;
            }
            else if (val == UNDEF) setLiteralToTrue(lit);
        }

    // DPLL algorithm
    while (true) {
        uint cause;
        while (propagateGivesConflict(cause)) {
            if (decisionLevel == 0) {
                gettimeofday(&end, NULL);
                cout << (end.tv_sec+((double)end.tv_usec/1000000))-(start.tv_sec+((double)start.tv_usec/1000000)) << endl;
                cout << "UNSATISFIABLE" << endl;
                return 10;
            }
            backjump(cause);
            //backtrack();
        }
        int decisionLit = getNextDecisionLiteral();
        if (decisionLit == 0) {
            gettimeofday(&end, NULL);
            cout << (end.tv_sec+((double)end.tv_usec/1000000))-(start.tv_sec+((double)start.tv_usec/1000000)) << endl;
            checkmodel(); cout << "SATISFIABLE" << endl;
            return 20;
        }
        // start new decision level:
        modelStack.push_back(0);  // push mark indicating new DL
        ++indexOfNextLitToPropagate;
        ++decisionLevel;
        setLiteralToTrue(decisionLit);    // now push decisionLit on top of the mark
    }
}  
