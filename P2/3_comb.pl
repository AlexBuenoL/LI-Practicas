% permutacio(L,P) "P és una permutació de L"
permutacio([], []).
permutacio(L,  [X|P]) :- select(X,L,R), permutacio(R,P).

% subcjt(L,S) "S és un subconjunt de L"
subcjt([],    []   ).
subcjt([X|C], [X|S]) :- subcjt(C,S).
subcjt([_|C], S    ) :- subcjt(C,S).

% xifres(L,N) "a partir dels números de la llista L es forma una expressió
%              amb sumes, restes i productes que s'avalua al valor N"
xifres(L,N) :-
    subcjt(L,S), permutacio(S,P), expressio(P,E),
    N is E, write(E), nl, fail.

% expressió(L,E) "E és una expressió formada amb les xifres de la llista L"
expressio([X],X).
expressio(L,E1+E2) :-
    append(L1,L2,L), L1\=[], L2\=[],
    expressio(L1,E1), expressio(L2,E2).
expressio(L,E1-E2) :-
    append(L1,L2,L), L1\=[], L2\=[],
    expressio(L1,E1), expressio(L2,E2).
expressio(L,E1*E2) :-
    append(L1,L2,L), L1\=[], L2\=[],
    expressio(L1,E1), expressio(L2,E2).
