% pert(E,L) "l'element E pertany a la llista L"
pert(X,[X|_]).                 % o bé X és el primer, o bé
pert(X,[_|L]) :- pert(X,L).    % pertany a la llista de la cua

% concat(L1,L2,L3) "la concatenació les llistes L1 i L2 és la llista L3"
concat([],L,L).
concat([X|L1],L2,[X|L3]) :- concat(L1,L2,L3).

% També:
% pert(X,L):- concat(_,[X|_],L).

% pert_amb_resta(E,L,R) "l'element E pertany a la llista L,
%                        i la llista R conté els elements de L excepte E"
pert_amb_resta(X,L,Resta) :- concat(L1,[X|L2],L), concat(L1,L2,Resta).

% Alternativa una mica més eficient:
% pert_amb_resta(X,[X|L],L).
% pert_amb_resta(X,[Y|L],[Y|R]) :- pert_amb_resta(X,L,R).
