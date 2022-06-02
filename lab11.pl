% 1.1
% dropAny(?Elem,?List,?OutList)

dropAny(X, [Y | T], T):- copy_term(X, Y).
dropAny(X, [H | Xs], [H | L]) :- dropAny(X, Xs, L).

% 1.2
% dropFirst: drops only the first occurrence

dropFirst(X, [Y | T], T):-!, copy_term(X, Y).
dropFirst(X, [H | Xs], [H | L]) :- dropFirst(X, Xs, L).

% 1.3
% dropLast: drops only the last occurrence (showing no alternative results)

dropLast(X, [H | Xs], [H | L]) :- dropLast(X, Xs, L).
dropLast(X, [Y | T], T):-!, copy_term(X, Y).

% 1.4
% dropAll: drop all occurrences, returning a single list as result

dropAll([], X, []).
dropAll([Y | T], X, L):- copy_term(X, Y), !,  dropAll(T, X, L).
dropAll([H | Xs], X, [H | L]) :- dropAll(Xs ,X, L).

% 2.1
% fromList(+List,-Graph)

fromList([_],[]).
fromList([H1,H2|T],[e(H1,H2)|L]):- fromList([H2|T],L).

% 2.2
% fromCircList(+List,-Graph)

fromCircList([H],X, [e(H, X)]).
fromCircList([H1,H2|T], X, [e(H1,H2)|L]):- fromCircList([H2|T], X, L).
fromCircList([H|T],G):- fromCircList([H|T],H, G).

% 2.3
% in_degree(+Graph, +Node, -Deg)
%
% Deg is the number of edges leading into Node

in_degree([], _ , 0).
in_degree([e(_, N)| T], N, D):- in_degree(T, N, D1), D is D1 +1.
in_degree([H| T], N, D):- in_degree(T, N, D).

% 2.4
% dropNode(+Graph, +Node, -OutGraph)
dropNode(G, N, OG):- dropAll(G, e(N,_),G2),  dropAll(G2,e(_,N),OG).


% 2.5
% 
% reaching(+Graph, +Node, -List)
% all the nodes that can be reached in 1 step from Node
% possibly use findall , looking for e(Node ,_) combined
% with member(?Elem,?List)

reaching(G, N, L):- findall(X, member(e(N, X),G), L).


% 2.6
% anypath(+Graph, +Node1, +Node2, -ListPath)
% a path from Node1 to Node2
% if there are many path , they are showed 1-by -1
% anypath(G, NS, NE, [e(NS,NE)]):- member(e(NS,NE), G).
anypath(G,N,N, []).
anypath(G, NS, NE, [e(NS, N)|L]):- reaching(G, NS, LN), member(N, LN), anypath(G, N, NE, L).

% 2.7
% allreaching(+Graph, +Node, -List)
% all the nodes that can be reached from Node
% Suppose the graph is NOT circular!
% Use findall and anyPath!

dropequal([],[]).
dropequal([H | T], L):- member(H,T), dropequal(T, L), !.
dropequal([H | T], [H|L]):- dropequal(T, L).

allreaching(G, N, LU):-  findall(X, anypath(G, N, X, [_|_]), L), dropequal(L, LU) .

% 2.8
% Adapt that code to create a graph for the predicates implemented so far
% interval(A, B, A).
% interval(A, B, X):- A2 is A+1, A2 < interval(A, B, A).
interval(A, B, A).
interval(A, B, X):- A2 is A+1, A2 < B, interval(A2, B, X).

neighbour(A, B, A, B2):- B2 is B+1.
neighbour(A, B, A, B2):- B2 is B-1. 
neighbour(A, B, A2, B):- A2 is A+1. 
neighbour(A, B, A2, B):- A2 is A-1.

generatelink(N, M, e(IN, EN)):-
	interval(0, N, X),
	interval(0, M, Y),
	neighbour(X, Y, XN, YN),
	interval(0, N, XN),
	interval(0, M, YN),
	IN is X * M + Y,
	EN is XN * M + YN.


generategrap(N, M, L):-
	findall(X, generatelink(N, M, X), L).
	
% generate all paths from a node to another, limiting the maximum number of hops


limitedanypath(G, NO, NO, N, []).
limitedanypath(G, NS, NE, H, [e(NS, N)|L]):- reaching(G, NS, LN), member(N, LN), H >0, H1 is H - 1, limitedanypath(G, N, NE, H1, L).

allpath(N, H, P):-
	generategrap(N, G),
	interval(0, N, NS),
	interval(0, N, NE),
	NS =\= NE,
	limitedanypath(G, NS, NE, H, P).

% 3.1
% next(@Table,@Player,-Result,-NewTable)
% Table is a representation of a TTT table where players x or o are playing
% Player (either x or o) is the player to move
% Result is either win(x), win(o), nothing, or even
% NewTable is the table after a valid move
% Should find a representation for the Table
% Calling the predicate should give all results
cell(X, Y, V).

notmember(E, []).
notmember(E, [H|T]):- E\=H, notmember(E, T).


win(T, P):- member(cell(X, 0, P), T),  member(cell(X, 1, P), T), member(cell(X, 2, P), T).
win(T, P):- member(cell(0,Y, P), T),  member(cell( 1, Y, P), T), member(cell( 2,Y, P), T).
win(T, P):- member(cell(0, 0, P), T),  member(cell( 1, 1, P), T), member(cell( 2,2, P), T).
win(T, P):- member(cell(2, 0, P), T),  member(cell( 1, 1, P), T), member(cell( 0,2, P), T).

next(T, P, win(W), T):- win(T, W).
next(T, P, even, T):- length(T, 9), not(win(T, _)).

next([], P, nothing, [cell(X, Y, P)]):-  
	interval(0, 3, Y),
	interval(0, 3, X).

next(T, P, win(P), L):- 
	next(T, P, L),
	win(L, P).

next(T, P, even, L):- 
	next(T, P, L),
	length(L, 9), 
	not(win(L, P)).

next(T, P, nothing, L):- 
	next(T, P, L),
	length(L, N), 
	N < 9,
	not(win(L, P)).
	
next(T, P, L):- 
	interval(0, 3, Y),
	interval(0, 3, X),
	notmember(cell(X, Y, _), T), 
	append(T, [cell(X, Y, P)], L).
	
% 3.2
% game(@Table,@Player,-Result,-TableList) 
% TableList is the sequence of tables until Result win(x), win(o) or even
nextPlayer(o, x).
nextPlayer(x, o).

game(T, P, win(X), T):- next(T, P, win(X), T).
game(T, P, even, T):- next(T, P, even, T).
game(T, P, R, TL):- next(T, P, R1, T1), T1 \= T, nextPlayer(P, PN), game(T1, PN , R, TL).


% 4
% An example theory for simple resolution
rule(a, []). 			% means: a.
rule(b, []). 			% means: b.
rule(d, []). 			% means: d.
rule(c, [a,b]). 	% means:c:- a,b.
rule(c, [a,d]). 	% means:c:- a,d.
rule(c, [c]).   	% means:c:- c.
rule(d, [d]).			% means:d:-d

% next(+RI, -RO) relates
% a resolvent is a list of goals
% e.g.: next([c,a], R) -> R/[a,b,a]; R/[a,d,a]; R/[c,a]
next([G|T], R) :- rule(G,B), append(B,T,R).

% 4.1
% trace(+RI, -LR) relates a resolvent with all success trace
% a success trace is a list of resolvents, ending with []
% e.g.: trace([c], L)
% -> L/[[c],[a,b],[b],[]]; L/[[c],[a,d],[d],[]]; ...
trace([], [[]]).
trace(G, R):- next(G, B), trace(B, R1), append([G],R1,R).

% 4.1
% traces are given in opposite order than one would expect
traceReverse([], [[]]).
traceReverse(G, R):- next(G, B), traceReverse(B, R1), append(R1,[G],R).

% 4.1
% if because of a loop a trace is becoming longer than 100, it is just
% discarded
traceLimited([], [[]]).
traceLimited(G, R):- traceLimited(G, 0, R).
traceLimited([], N, [[]]):- N < 100.
traceLimited(G, N, R):- N < 100, next(G, B), N1 is N +1, traceLimited(B, N1, R1), append([G], R1,R).

% 4.1
% solutions are explored breadth firts, not depth first
tuple(T, R).
factory(T, R, tuple(T, R)).

traceBreathFirst(I, R):- traceBreathFirst1([tuple(I, [I])], R).
traceBreathFirst1([tuple([], T)| _], T).
traceBreathFirst1([tuple([], _)| T], R):-traceBreathFirst1(T, R).
traceBreathFirst1([tuple(I, N)| T], R):- step(I,N, T,  Q), traceBreathFirst1(Q, R).

step([G|T], E, Q, R):- findall(X, (rule(G, N), append(N, T, S), append(E, [S], R1), factory(S, R1, X)), L),
 append(Q, L, R).




test([],0).
test(G, R):- test(G,R).