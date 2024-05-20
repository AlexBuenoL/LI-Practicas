#include <iostream>
#include <stdlib.h>
#include <algorithm>
#include <vector>
using namespace std;

#define UNDEF -1
#define TRUE 1
#define FALSE 0

typedef pair<int,int> litOccurs;

uint numVars;
uint numClauses;
vector<vector<int> > clauses;
vector<int> model;
vector<int> modelStack;
uint indexOfNextLitToPropagate;
uint decisionLevel;

vector<vector<int> > posLiteralClauses;
vector<vector<int> > negLiteralClauses;
vector<litOccurs> occurList;
vector<double> conflicts_cont; 
int conflicts = 0;


void readClauses( ){
  // Skip comments
  char c = cin.get();
  while (c == 'c') {
    while (c != '\n') c = cin.get();
    c = cin.get();
  }  
  // Read "cnf numVars numClauses"
  string aux;
  cin >> aux >> numVars >> numClauses;
  posLiteralClauses = negLiteralClauses = vector<vector<int> >(numVars+1);
  conflicts_cont = vector<double>(numVars+1);
  clauses.resize(numClauses);  

  for (uint i = 0; i < numClauses; ++i) {
    int lit;
    while (cin >> lit and lit != 0) {
      clauses[i].push_back(lit);
      if (lit > 0) posLiteralClauses[lit].push_back(i);
      else negLiteralClauses[-lit].push_back(i);
    }
  }  
  for (uint i = 1; i <= numVars; ++i) {
    int occurs = posLiteralClauses[i].size() + negLiteralClauses[i].size();
    occurList.push_back(litOccurs(i, occurs));
  }  
  sort(occurList.begin(), occurList.end(), [](const litOccurs& a, const litOccurs& b) {return a.second > b.second; });
}


int currentValueInModel(int lit){
  if (lit >= 0) return model[lit];
  else {
    if (model[-lit] == UNDEF) return UNDEF;
    else return 1 - model[-lit];
  }
}


void setLiteralToTrue(int lit){
  modelStack.push_back(lit);
  if (lit > 0) model[lit] = TRUE;
  else model[-lit] = FALSE;		
}


bool propagateGivesConflict ( ) {
  while ( indexOfNextLitToPropagate < modelStack.size() ) {
    int l = modelStack[indexOfNextLitToPropagate];
    ++indexOfNextLitToPropagate;
    if (l < 0) {
      for (uint i = 0; i < posLiteralClauses[-l].size(); ++i) {
        bool someLitTrue = false;
        int numUndefs = 0;
        int lastLitUndef = 0;
        int c = posLiteralClauses[-l][i];
        for (uint k = 0; not someLitTrue and k < clauses[c].size(); ++k){
          int val = currentValueInModel(clauses[c][k]);
          if (val == TRUE) someLitTrue = true;
          else if (val == UNDEF){ ++numUndefs; lastLitUndef = clauses[c][k]; }
        }
        if (not someLitTrue and numUndefs == 0) { // conflict! all lits false
          ++conflicts;
          ++conflicts_cont[-l];
          if (conflicts % 10000 == 0) {
            for (uint j = 0; j < conflicts_cont.size(); ++j) conflicts_cont[j] /= 2;
          }
          return true; 
        }
        else if (not someLitTrue and numUndefs == 1) setLiteralToTrue(lastLitUndef);	
      }    
    } else {
      for (uint i = 0; i < negLiteralClauses[l].size(); ++i) {
        bool someLitTrue = false;
        int numUndefs = 0;
        int lastLitUndef = 0;
        int c = negLiteralClauses[l][i];
        for (uint k = 0; not someLitTrue and k < clauses[c].size(); ++k){
          int val = currentValueInModel(clauses[c][k]);
          if (val == TRUE) someLitTrue = true;
          else if (val == UNDEF){ ++numUndefs; lastLitUndef = clauses[c][k]; }
        }
        if (not someLitTrue and numUndefs == 0) { // conflict! all lits false
          ++conflicts;
          ++conflicts_cont[l];
          if (conflicts % 10000 == 0) {
            for (uint j = 0; j < conflicts_cont.size(); ++j) conflicts_cont[j] /= 2;
          }
          return true; 
        }
        else if (not someLitTrue and numUndefs == 1) setLiteralToTrue(lastLitUndef);	
      }    
    }
    
  }
  return false;
}


void backtrack(){
  uint i = modelStack.size() -1;
  int lit = 0;
  while (modelStack[i] != 0){ // 0 is the DL mark
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
int getNextDecisionLiteral(){
  // s escull el literal amb mex conflictes
  int litMaxConflicts = -1, maxConflicts = 0;
  for (uint i = 1; i <= conflicts_cont.size(); ++i) {
    if (conflicts_cont[i] > maxConflicts and model[i] == UNDEF) {
      litMaxConflicts = i;
      maxConflicts = conflicts_cont[i];
    } 
  }

  if (litMaxConflicts != -1) return litMaxConflicts;

  // si encara no tenen conflictes
  for (uint i = 0; i < occurList.size(); ++i) {
    if (model[occurList[i].first] == UNDEF) return occurList[i].first;
  }
  
  return 0; // reurns 0 when all literals are defined
}

void checkmodel(){
  for (uint i = 0; i < numClauses; ++i){
    bool someTrue = false;
    for (uint j = 0; not someTrue and j < clauses[i].size(); ++j)
      someTrue = (currentValueInModel(clauses[i][j]) == TRUE);
    if (not someTrue) {
      cout << "Error in model, clause is not satisfied:";
      for (uint j = 0; j < clauses[i].size(); ++j) cout << clauses[i][j] << " ";
      cout << endl;
      exit(1);
    }
  }  
}

int main(){ 
  readClauses(); // reads numVars, numClauses and clauses
  model.resize(numVars+1,UNDEF);
  indexOfNextLitToPropagate = 0;  
  decisionLevel = 0;
  
  // Take care of initial unit clauses, if any
  for (uint i = 0; i < numClauses; ++i)
    if (clauses[i].size() == 1) {
      int lit = clauses[i][0];
      int val = currentValueInModel(lit);
      if (val == FALSE) {cout << "UNSATISFIABLE" << endl; return 10;}
      else if (val == UNDEF) setLiteralToTrue(lit);
    }
  
  // DPLL algorithm
  while (true) {
    while ( propagateGivesConflict() ) {
      if ( decisionLevel == 0) { cout << "UNSATISFIABLE" << endl; return 10; }
      backtrack();
    }
    int decisionLit = getNextDecisionLiteral();
    if (decisionLit == 0) { checkmodel(); cout << "SATISFIABLE" << endl; return 20; }
    // start new decision level:
    modelStack.push_back(0);  // push mark indicating new DL
    ++indexOfNextLitToPropagate;
    ++decisionLevel;
    setLiteralToTrue(decisionLit);    // now push decisionLit on top of the mark
  }
}  
