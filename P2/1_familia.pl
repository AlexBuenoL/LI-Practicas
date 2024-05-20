% mare(F,M) "la mare de F és M"
mare(joan,angela).
mare(maria,angela).

% germana(A,G) "la germana d'A és G"
germana(angela,cris).
germana(angela,judit).

% tia(N,T) "la tia de N és T"
tia(N,T) :- mare(N,M), germana(M,T).
