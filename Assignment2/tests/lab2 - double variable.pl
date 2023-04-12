% 	Logic for Computer Scientists DD1351
% 	Lab 2, Proofchecking using Prolog
%
% 	Dilvan Sabir dilvans@kth.se
%	Arash Dabiri arashd@kth.se

:- set_prolog_stack(global, limit(8294967296)).

%	Desc:	The call function of our program.
verify(InputFileName) :-
    see(InputFileName), read(Prems), read(Goal), read(Proof),
    seen,
    valid_goal(Goal, Proof),
    valid_proof(Prems, Proof, Proof, []), !.

%	Desc:	Used to generate proofs with
%			Hypothetical and not necessary for  the lab.
generate(InputFileName,Proof) :-
    see(InputFileName), read(Prems), read(Goal), %read(Proof),
    seen,
	valid_proof(Prems, Proof, Proof, []),
	valid_goal(Goal, Proof).

% 	Desc:	Is last row of proof same thing as the goal?
valid_goal(Goal, Proof) :-
	last(Proof,Row),
	nth0(0,Row,RowNum),
	get_val_at_row(RowNum,Proof,Val),
    Goal = Val, !.

%----------------------------------------Main function----------------------------------------%

%	Desc:	Base case, regardless of anything, if the third parameter is empty then we call it quits.
% 			We also have a cut here because if we reach the end of the Premises list, we are done, we have no more premises avaliable to us to check for.
valid_proof(_, _, [], _) :- !.

%	Desc:	Premise case, If the row is a premise, then call valid_premise to ensure premise is valid.
valid_proof(Prems, Proof, [[Row, Val, premise] | Tail], PreviouslyChecked) :-
	memberchk(Val,Prems),
    valid_proof(Prems, Proof, Tail, [[Row, Val, premise] | PreviouslyChecked]).

%----------------------------------------Boxes----------------------------------------%
%	A box is defined as a list inside the proof-list
%	With an "assumption" as the rule of that row
valid_proof(Prems, Proof, [[[Row, Val, assumption] | BoxT] | Tail], PreviouslyChecked) :-
    valid_proof(Prems, Proof, BoxT, [[Row, Val, assumption] | PreviouslyChecked]),
    valid_proof(Prems, Proof, Tail, [[[Row, Val, assumption] | BoxT] | PreviouslyChecked]).
%----------------------------------------Rules----------------------------------------%

%	Rule:	And-Introduction
%	Desc:	
valid_proof(Prems, Proof, [[Row, and(A,B), andint(A_row,B_row)] | Tail], PreviouslyChecked) :-
    get_val_at_row(A_row, PreviouslyChecked, A),
    get_val_at_row(B_row, PreviouslyChecked, B),
    valid_proof(Prems, Proof, Tail, [[Row, and(A,B), andint(A_row,B_row)] | PreviouslyChecked]).
	
%	Rule:	And-Elimination-1
%	Desc:	True when Val = 1st argument of AND-statement at row A_row
valid_proof(Prems, Proof, [[Row, Val, andel1(A_row)] | Tail], PreviouslyChecked) :-
    get_val_at_row(A_row, PreviouslyChecked, and(Val, _)),
    valid_proof(Prems, Proof, Tail, [[Row, Val, andel1(A_row)] | PreviouslyChecked]).

%	Rule:	And-Elimination-2
%	Desc:	True when Val = 2nd argument of AND-statement at row A_row
valid_proof(Prems, Proof, [[Row, Val, andel2(A_row)] | Tail], PreviouslyChecked) :-
    get_val_at_row(A_row, PreviouslyChecked, and(_, Val)),
    valid_proof(Prems, Proof, Tail, [[Row, Val, andel2(A_row)] | PreviouslyChecked]).


%	Rule:	Or-Introduction-1
%	Desc:	1st argument gets introduced
%			True when 1st argument of Val = value of row A_row
valid_proof(Prems, Proof, [[Row, or(A,B), orint1(A_row)] | Tail], PreviouslyChecked) :-
    get_val_at_row(A_row, PreviouslyChecked, A),
    valid_proof(Prems, Proof, Tail, [[Row, or(A,B), orint1(A_row)] | PreviouslyChecked]).

%	Rule:	Or-Introduction-2
%	Desc:	2nd argument gets introduced
%			True when 2nd argument of Val = value of row A_row
valid_proof(Prems, Proof, [[Row, or(A,B), orint2(A_row)] | Tail], PreviouslyChecked) :-
    get_val_at_row(A_row, PreviouslyChecked, B),
    valid_proof(Prems, Proof, Tail, [[Row, or(A,B), orint2(A_row)] | PreviouslyChecked]).


%	Rule:	Or-Elimination
%	Desc:	Is val of row R an OR statement? 
%			
valid_proof(Prems, Proof, [[Row, Val, orel(R, A_first_row, A_last_row, B_first_Row, B_last_row)] | Tail], PreviouslyChecked) :- 
    get_val_at_row(R, PreviouslyChecked, or(P,Q)),
    box_in_Range([A_first_row, P, _], PreviouslyChecked, BoxA),
    box_in_Range([B_first_Row, Q, _], PreviouslyChecked, BoxB),
	nth0(0,BoxA,[A_first_row, P, _]),
    nth0(0,BoxB,[B_first_Row, Q, _]),
    last(BoxA, [A_last_row, Val, _]),
    last(BoxB, [B_last_row, Val, _]),
    valid_proof(Prems, Proof, Tail, [[Row, Val, orel(R, R, A_last_row, B_first_Row, B_last_row)] | PreviouslyChecked]).


%	Rule:	Implication-Introduction
%	Desc:	
valid_proof(Prems, Proof, [[Row, imp(A_val,B_val), impint(A_row,B_row)] | Tail], PreviouslyChecked) :-
    box_in_Range([A_row, A_val, _], PreviouslyChecked, Box),
    nth0(0,Box,[A_row, A_val, _]),
    last(Box, [B_row, B_val, _]),
    valid_proof(Prems, Proof, Tail, [[Row, imp(A_val,B_val), impint(A_row,B_row)] | PreviouslyChecked]).

%	Rule:	Implication-Elimination
%	Desc:	
valid_proof(Prems, Proof, [[Row, Val, impel(A_row,B_row)] | Tail], PreviouslyChecked) :-
    get_val_at_row(A_row, PreviouslyChecked, A_val),
    get_val_at_row(B_row, PreviouslyChecked, imp(A_val, Val)),
    valid_proof(Prems, Proof, Tail, [[Row, Val, impel(A_row,B_row)] | PreviouslyChecked]).




%	Rule:	Negation-Introduction
%	Desc:	Is there a contradiction in the last row of the box?
valid_proof(Prems, Proof, [[Row, neg(A), negint(A_row,B_row)] | Tail], PreviouslyChecked) :-
    box_in_Range([A_row, A, _], PreviouslyChecked, Box),
	nth0(0,Box,[A_row, A, _]),
    last(Box, [B_row, cont, _]),
    valid_proof(Prems, Proof, Tail, [[Row, neg(A), negint(A_row,B_row)] | PreviouslyChecked]).

%	Rule:	Negation-Elimination
%	Desc:	Is contradiction valid?
%			Valid = val on row B_row = neg(val) from row A_row
valid_proof(Prems, Proof, [[Row, cont, negel(A_row,B_row)] | Tail], PreviouslyChecked) :-
    get_val_at_row(A_row, PreviouslyChecked, A),
    get_val_at_row(B_row, PreviouslyChecked, neg(A)),
    valid_proof(Prems, Proof, Tail, [[Row, cont, negel(A_row,B_row)] | PreviouslyChecked]).



%	Rule:	Double Negation-Introduction
%	Desc:	Is Val double negated value of value on row A_row ?
valid_proof(Prems, Proof, [[Row, neg(neg(Val)), negnegint(A_row)] | Tail], PreviouslyChecked) :-
    get_val_at_row(A_row, PreviouslyChecked, Val),
    valid_proof(Prems, Proof, Tail, [[Row, Val, negnegint(A_row)] | PreviouslyChecked]).

%	Rule:	Double Negation-Elimination
%	Desc:	Is value on row A_row double negated value of Val?
valid_proof(Prems, Proof, [[Row, Val, negnegel(A_row)] | Tail], PreviouslyChecked) :-
    get_val_at_row(A_row, PreviouslyChecked, neg(neg(Val))), 
    valid_proof(Prems, Proof, Tail, [[Row, Val, negnegel(A_row)] | PreviouslyChecked]).


%	Rule:	Contradiction-Elimination
%	Desc:	Contradiction on row A_row?
valid_proof(Prems, Proof, [[Row, Val, contel(A_row)] | Tail], PreviouslyChecked) :-
    get_val_at_row(A_row, PreviouslyChecked, cont),
    valid_proof(Prems, Proof, Tail, [[Row, Val, contel(A_row)] | PreviouslyChecked]).


%	Rule:	Copy
%	Desc:	Checks if Val is the same as the value on row A_row
valid_proof(Prems, Proof, [[Row, Val, copy(A_row)] | Tail], PreviouslyChecked) :-
    get_val_at_row(A_row, PreviouslyChecked, Val),
    valid_proof(Prems, Proof, Tail, [[Row, Val, copy(A_row)] | PreviouslyChecked]).
<<<<<<< HEAD:tests/lab2 - double variable.pl
	
%----------------------------------------Dervied Rules----------------------------------------%
=======


%	------------------------------------------------Derived Rules------------------------------------------------

>>>>>>> 0f3de118b4c140acff1fe2cf7c0f51df4292923a:tests/lab2_v2.pl
%	Rule:	Modus Tollens(MT) 
%	Desc:	
valid_proof(Prems, Proof, [[Row, neg(Val), mt(A_row,B_row)] | Tail], PreviouslyChecked) :-
    get_val_at_row(A_row, PreviouslyChecked, imp(Val,B)),
    get_val_at_row(B_row, PreviouslyChecked, neg(B)),
    valid_proof(Prems, Proof, Tail, [[Row, neg(Val), mt(A_row,B_row)] | PreviouslyChecked]).

%	Rule:	Proof By Contradiction(PBC)
%	Desc:	Has not(val) been assumed as assumption in a box
% 			AND we have ended with a contradiction?
valid_proof(Prems, Proof, [[Row, Val, pbc(A_row, B_row)] | Tail], PreviouslyChecked) :-
    box_in_Range([A_row, neg(Val), _], PreviouslyChecked, Box),
    nth0(0,Box,[A_row, neg(Val), _]),
    last(Box, [B_row, cont, _]),
    valid_proof(Prems, Proof, Tail, [[Row, Val, pbc(A_row,B_row)] | PreviouslyChecked]). 


%	Rule:	Law of Excluded Middle(LEM)
%	Desc:	Is value = (Q or not(Q)) ?
valid_proof(Prems, Proof, [[Row, or(A, B), lem] | Tail], PreviouslyChecked) :-
    A = neg(B) ; B = neg(A),
    valid_proof(Prems, Proof, Tail, [[Row, or(A,B), lem] | PreviouslyChecked]).

%----------------------------------------Helper functions----------------------------------------%
%	True when the given proof-row matches a box in the given range.
<<<<<<< HEAD:tests/lab2 - double variable.pl
%	Empty PreviouslyCheckedList will result in failure
%	If box is undeclared, attempt will be made to unify with matched box in the PreviouslyCheckedList
=======
%	Empty PreviouslyChecked results in failure
%	If box is undeclared, attempt will be made to unify with matched box in the PreviouslyChecked list.
>>>>>>> 0f3de118b4c140acff1fe2cf7c0f51df4292923a:tests/lab2_v2.pl
box_in_Range(_, [], _) :- fail.
box_in_Range([Nr, Val, _], [[[Nr, Val, _] | BoxT] | _], [[Nr, Val, _] | BoxT]).
box_in_Range([Nr, Val, _], [ _ | T], Box) :- 
    box_in_Range([Nr, Val, _], T, Box).

<<<<<<< HEAD:tests/lab2 - double variable.pl
%	Recieves value/rowNumber at specfic place in list.
%	Attempts to unify the value and/or the row number with an element in the given PreviouslyCheckedList. 
=======
%	Gets row or value at the Proof-row of the previouslyChecked-list
%	Attempts to unify the value and/or the row number with an element in the given range-list. 
>>>>>>> 0f3de118b4c140acff1fe2cf7c0f51df4292923a:tests/lab2_v2.pl
get_val_at_row(_, [], _) :- fail.
get_val_at_row(Nr, [[Nr, Val, _] | _], Val).
get_val_at_row(Nr, [_ | T], Row) :- get_val_at_row(Nr, T, Row).   
