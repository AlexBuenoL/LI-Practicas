p(L, R) :- findall([X,Y], (member(X,L), Y is X+1), R).