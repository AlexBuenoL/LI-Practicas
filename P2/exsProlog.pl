%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Notació:
%%   * "donat N" significa que l'argument N estarà instanciat inicialmente.
%%   * "ha de ser capaç de generar totes les respostes possibles" significa que
%%     si hi ha backtracking ha de poder generar la següent resposta, com el
%%     member(E,L) que per una llista L "donada" pot generar tots els elements E.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% En LI adapterem la "Notation of Predicate Descriptions" de SWI-Prolog per
%% descriure els predicats, prefixant cada argument amb un d'aquests 3 símbols:
%%   '+' quan l'argument ha d'estar necessàriament instanciat (no pot ser una
%%       variable sense instanciar). Pot ser ground (f(a) o 34)" o no (X+1 o g(a,Y)).
%%       Quan parlem de "donada L", llavors especficarem +L en la *descripció*.
%%       Per exemple, l'argument de +L del predicat esta_ordenada(+L).
%%   '-' quan l'argument ha de ser necessàriament una variable que quedarà
%%       instanciada, al satisfer-se el predicat, amb un cert terme que podem
%%       veure com un "resultat".
%%       Per exemple, l'argument -F en el predicat fact(+N,-F) que per un N donat,
%%       se satisfà fent que F sigui el valor N!.
%%   '?' quan s'accepta que l'argument pugui estar instanciat o no.
%%       Es tracta dels casos en que es diu "ha de poder generar la S i també
%%       comprovar una S donada". Llavors especificarem ?S en la *descripció*.
%%       Per exemple, l'argument ?S de suma(+L,?S).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% En aquests exercicis feu servir els predicats:
%%   * member(E,L)         en lloc de  pert(E,L)
%%   * append(L1,L2,L3)    en lloc de  concat(L1,L2,L3)
%%   * select(E,L,R)       en lloc de  pert_amb_resta(E,L,R)
%%   * permutation(L,P)    en lloc de  permutacio(L,P)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



% PROB. A =========================================================
% Escriu un predicat
% prod(+L,?P)  que signifiqui: P és el producte dels
% elements de la llista de enters donada L. Ha de poder generar la
% P i també comprovar una P donada
prod([],1).
prod([X|L],P) :- prod(L,P1), P is P1*X.



% PROB. B =========================================================
% Escriu un predicat
% pescalar(+L1,+L2,?P) que signifiqui: P és el producte escalar dels
% vectors L1 i L2, on els vectors es representen com llistes
% d'enters. El predicat ha de fallar si els dos vectors
% tenen longituds diferents.
pescalar([], [], 0).
pescalar([X|L1], [Y|L2], P) :- pescalar(L1,L2,P1), P is X*Y + P1.



% PROB. C =========================================================
% Representant conjunts com llistes sense repeticions, escriu
% predicats per les operacions d'intersecció i unió de conjunts donats

% intersection(+L1,+L2,?L3)
intersection([], _, []).
intersection([X|L1], L2, [X|I]) :- member(X, L2), !, intersection(L1, L2, I). % A L3 solo le añades los numeros de L1 que es estan tmb en L2
intersection([_|L1], L2, I) :- intersection(L1, L2, I).


% union(+L1,+L2,?L3)
union([], L, L).
union([X|L1], L2, U) :- member(X,L2), !, union(L1, L2, U).
union([X|L1], L2, [X|U]) :- union(L1, L2, U).
 


% PROB. D =========================================================
% Usant append/3, escriu un predicat per calcular l'últim 
% element d'una llista donada, i un altre per calcular la llista
% inversa d'una llista donada.

% ultim(+L,?E)
ultim(L, X) :- append(_, [X], L), !.


% inversa(+L1,?L2)
inversa([], []).
inversa([X], [X]).
inversa(L, [U|LI]) :- append(L2, [U], L), inversa(L2, LI), !.



% PROB. E =========================================================
% Escriu un predicat
% fib(+N,?F) que signifiqui: F és l'N-éssim nombre de Fibonacci
% per a la N donada. Aquests nombres es defineixen així:
% fib(1) = 1, fib(2) = 1, i si N > 2 llavors
% fib(N) = fib(N-1) + fib(N-2)
fib(1, 1).
fib(2, 1).
fib(N, F) :- N1 is N-1, fib(N1, F1), 
             N2 is N-2, fib(N2, F2), 
             F is F1 + F2, !.



% PROB. F =========================================================
% Escriu un predicat
% dados(+P,+N,-L) que signifiqui: la llista L expressa una forma de
% sumar P punts llançant N daus. Per exemple: si P és 5, i
% N és 2, una solució seria [1,4] (noteu que la longitud de L és N.
% Tant P com N venen instanciats. El predicat deu ser capaç de
% generar totes les solucions possibles.
dados(0,0,[]) :- !.
dados(P, N, [X|L]) :- N > 0,
                    between(1, 6, X),
                    P1 is P-X, 
                    N1 is N-1,
                    dados(P1, N1, L).

                      
                    
% PROB. G =========================================================
% Escriu un predicat
% suma_la_resta(+L) que, donada una llista d'enters L, es satisfà si
% existeix algun element en L que és igual a la suma de la resta
% d'elements de L, i que altrament falla.
% Escriu abans un predicat
% suma(+L,?S) que, donada una llista d'enters L, se satisfà si S
% és la suma dels elements d'L.

% suma(+L,?S)
suma([], 0).
suma([X], X).
suma([X|L], S) :- suma(L, S1), S is S1 + X.


% suma_la_resta(+L)
suma_la_resta(L) :- select(X,L,R), suma(R, X), !.



% PROB. H =========================================================
% Escriu un predicat
% card(+L) que, donada una llista d'enters L, escriba la llista
% que, para cada element d'L, diu quantes vegades surt aquest
% element en L.
% Per exemple, si fem la consulta
% card( [1,2,1,5,1,3,3,7] )  l'intèrpret escriurà:
% [[1,3],[2,1],[5,1],[3,2],[7,1]].
card(L):- card2(L, Lres), write(Lres).
card2(L, Res) :- findall([X,A], (member(X,L), findall(E, (member(E,L), E=X), LA), length(LA, A)), R), list_to_set(R, Res).



% PROB. I ========================================================
% Escriu un predicat
% esta_ordenada(+L) que signifiqui: la llista L de nombres enters
% està ordenada de menor a major.
% Per exemple, a la consulta:
% ?- esta_ordenada([3,45,67,83]).
% l'intèrpret respon yes, i a la consulta:
% ?- esta_ordenada([3,67,45]).
% respon no.
esta_ordenada([]).
esta_ordenada([_]).
esta_ordenada([X|L]) :- append([F], _, L),
                        X =< F,
                        esta_ordenada(L), !.



% PROB. J ========================================================
% Escriu un predicat
% palíndroms(+L) que, donada una llista de lletres L escrigui
% totes les permutacions dels seus elements que siguin palíndroms
% (capicues). Per exemple, amb la consulta palindroms([a,a,c,c])
% s'escriu [a,c,c,a] i [c,a,a,c]
% (possiblement diverses vegades, no cal que eviteu les repeticions).
palindroms([], []).
palindroms(L) :- permutation(L, P),
                 es_palindrom(P),
                 write(P).

es_palindrom([]).
es_palindrom([_]).
es_palindrom([P|L]) :- append(L1, [U], L),
                       P = U,
                       es_palindrom(L1).



% PROB. K ========================================================
% Volem obtenir en Prolog un predicat
% dom(+L) que, donada una llista L de fitxes de dominó (en el format
% indicat abaix), escrigui una cadena de dominó fent servir *totes*
% les fitxes de L, o escrigui "no hi ha cadena" si no és possible.
% Per exemple,
% ?- dom( [ f(3,4), f(2,3), f(1,6), f(2,2), f(4,2), f(2,1) ] ).
% escriu la cadena correcta:
% [ f(2,3), f(3,4), f(4,2), f(2,2), f(2,1), f(1,6) ].
%
% També podem "girar" alguna fitxa como f(N,M), reemplaçant-la
% per f(M,N). Així, per:
% ?- dom( [ f(4,3), f(2,3), f(1,6), f(2,2), f(2,4), f(2,1) ] ).
% només hi ha cadena si es gira alguna fitxa (per exemple, hi ha
% mateixa cadena d'abans).
%
% El següent programa Prolog encara no té implementat els possibles
% girs de fitxes, ni té implementat el predicat ok(P), que
% significa: P és una cadena de dominó correcta (tal qual,
% sense necessitat de girar cap fitxa):

dom(L) :- p(L,P), ok(P), write(P), nl.
dom(_) :- write('no hi ha cadena'), nl.

% a) Escriu el predicat ok(+P) que falta.
ok([]).
ok([f(_,_)]).
ok([f(_,B)|L]) :- append([f(A2,_)], _, L), B=A2, ok(L).


% b) Estén el predicat p/2 per a que el programa també pugui
%    fer cadenes girant alguna de les fitxes de l'entrada.
p([],[]).
p(L,[X|P]) :- select(X,L,R), p(R,P).
p(L,[f(A,B)|P]) :- select(f(B,A),L,R), p(R,P).



% PROB. L ========================================================
% Write in Prolog a predicate flatten(+L,?F) that ``flattens''
% (cat.: ``aplana'') the list F as in the example:
% ?- flatten( [a,b,[c,[d],e,[]],f,[g,h]], F ).
% F = [a,b,c,d,e,f,g,h]
flatten([],[]).
flatten([X|L], R) :- flatten(X, E), flatten(L, R2), append(E, R2, R), !.
flatten(X, [X]).



% PROB. M ========================================================
% Consider two groups of 10 people each. In the first group,
% as expected, the percentage of people with lung cancer among smokers
% is higher than among non-smokers.
% In the second group, the same is the case.
% But if we consider the 20 people of the two groups together, then
% the situation is the opposite: the proportion of people with
% lung cancer is higher among non-smokers than among smokers!
% Can this be true? Write a little Prolog program to find it out.

main :-
    % Group 1
    between(0,3,SC1),    % SC1:   "no.    smokers with    cancer group 1"
    between(0,3,SNC1),   % SNC1:  "no.    smokers with no cancer group 1"
    between(0,3,NSC1),   % NSC1:  "no. no smokers with    cancer group 1"
    between(0,3,NSNC1),  % NSNC1: "no. no smokers with no cancer group 1"
    10 is SC1+SNC1+NSC1+NSNC1,  

    PCF1 is SC1 / (SC1 + SNC1),      % PCF1:  porcentaje de cancer entre fumadores grupo 1
    PCNF1 is NSC1 / (NSC1 + NSNC1),  % PCNF1: porcentaje de cancer entre no fumadores grupo 1
    PCF1 > PCNF1,  

    % Group 2
    between(0,3,SC2),    % SC2:   "no.    smokers with    cancer group 2"
    between(0,3,SNC2),   % SNC2:  "no.    smokers with no cancer group 2"
    between(0,3,NSC2),   % NSC2:  "no. no smokers with    cancer group 2"
    between(0,3,NSNC2),  % NSNC2: "no. no smokers with no cancer group 2"
    10 is SC2+SNC2+NSC2+NSNC2,
    
    PCF2 is SC2 / (SC2 + SNC2),      % PCF2:  porcentaje de cancer entre fumadores grupo 2
    PCNF2 is NSC2 / (NSC2 + NSNC2),  % PCNF2: porcentaje de cancer entre no fumadores grupo 2
    PCF2 > PCNF2,  

    FumadoresTot is SC1 + SC2 + SNC1 + SNC2,
    PorcCancerFumadores is (SC1 + SC2) / FumadoresTot,

    NoFumadoresTot is NSC1 + NSC2 + NSNC1 + NSNC2,
    PorcCancerNoFumadores is (NSC1 + NSC2) / NoFumadoresTot,

    PorcCancerNoFumadores > PorcCancerFumadores.


    
