% Load model, initial state and formula from file.
verify(Input) :-
    see(Input), read(T), read(L), read(S), read(F), seen,
    check(T, L, S, [], F).

% check(T, L, S, U, F)
% T - The transitions in form of adjacency lists
% L - The labeling
% S - Current state
% U - Currently recorded states
% F - CTL Formula to check.

:- discontiguous(check/5).
% Desc:	Does F(CTL Formula) to check exist in S(Current state)
%		And does S exist in L(Labeling)?
check(_, L, S, [], F)      :-
  member([S,Atoms], L),
  member(F,Atoms).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%	Negation
% 	Desc:	Negation handling, if negation, try to unify with not(check(F))
check(T, L, S, [], neg(F)) :-
  not(check(T,L,S,[],F)).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% 	And
% 	Desc:	True IFF check(F) AND check (G)	unify.
check(T, L, S, [], and(F,G)) :-
  check(T,L,S,[],F),
  check(T,L,S,[],G).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% 	Or
% 	Desc:	True IFF check(F) OR(Inclusive) check (G)	unify.
check(T,L,S,[],or(F,G)) :-
  check(T,L,S,[],F);
  check(T,L,S,[],G).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%	All neXt - Applies on all next neighbors of S
% 	Desc:	ax -  
check(T,L,S,[],ax(F)) :-
  member([S, Neighbors], T),
  ax(T,L,Neighbors,[],F).

%	Recurse through list until no tail. For each item check(F)
ax(T,L,[S0,S1|Sn],[],F) :-
  check(T,L,S0,[],F),
  ax(T,L,[S1|Sn],[],F).

% 	If no tail then just do once. 
ax(T,L,[S0|[]],[],F) :-
  check(T,L,S0,[],F).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%	Exists neXt	- Applies on at least one neighbor of S
% 	Desc:	Unifies a list of S(Current state) and its neighbors from T(Transitions)
% 			True IFF - L0 exists in Neighbors which are the adjacent transitions to S in T
check(T, L, S, [], ex(F)) :-
  member([S,Neighbors],T),
  member(L0,Neighbors),
  check(T,L,L0,[],F).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%	All Globally - Applies on all paths(and subpaths) starting from and including S
% 	Desc:	
check(T,L,S,U,ag(F)) :-
  %Make sure we've not been here before
  not(member(S, U)),
  %Make sure it applies in Current State
  check(T,L,S,[],F),
  %Find neighbors of S
  member([S,Neighbors],T),
  %Call upon ag on S's neighbors
  ag(T,L,Neighbors,[S|U],F).
%	Recurse through list until no tail. For each item check(ag(F))
ag(T,L,[S0,S1|Sn],U,F) :-
  check(T,L,S0,U,ag(F)),
  ag(T,L,[S1|Sn],U,F).
% 	If no tail then just do once. 
ag(T,L,[S0|[]],U,F) :-
  check(T,L,S0,U,ag(F)).
%	Make sure we visit everything
check(_,_,S,U,ag(_)) :-
  member(S,U).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%	Exists Globally	- Applies on one path(and subpaths) starting from and including S
% 	Desc:	
% 	Have we been everywhere?
check(_,_,S,U, eg(_)) :-
  member(S,U).
check(T,L,S,U,eg(F)) :-
  %Make sure we've not been here before
  not(member(S,U)),
  %Make sure it applies in Current State
  check(T,L,S,[],F),
    %Find neighbors of S
  member([S,Neighbors],T),
  member(L0,Neighbors),
    %Make sure also applies in neighbors
  check(T,L,L0,[S|U],eg(F)).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%	Exists Finally - Applies either to S or on one of its neighbors.
%	Desc:	
check(T,L,S,U,ef(F)) :-
 %Make sure we've not been here before
  not(member(S,U)),
  %Make sure it applies in Current State
  (   check(T,L,S,[],F);
  %Inclusive OR
    %Make sure it applies its neighbors
  (member([S,Neighbors],T),
  member(L0,Neighbors),
  check(T,L,L0,[S|U],ef(F)))).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%	All Finally - Applies for S or all of its neighbors somewhere.
% AF
check(T,L,S,Visited,af(F)) :-
      %Make sure we've not been here before
  not(member(S,Visited)),
      %Make sure it applies in Current State
  (check(T,L,S,[],F);
  %Inclusive Or
      %Make sure it applies to Neighbors
   (member([S,Neighbors],T),
  af(T,L,Neighbors,[S|Visited],F))).
%	Recurse through list until no tail. For each item check(af(F))
af(T,L,[S0,S1|Sn],Visited,F) :-
  check(T,L,S0,Visited,af(F)),
  af(T,L,[S1|Sn],Visited,F).
% 	If no tail then just do once. 
af(T,L,[S0|[]],Visited,F) :-
  check(T,L,S0,Visited,af(F)).
