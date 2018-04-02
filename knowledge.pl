%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Description: Knowledge Base
%     Version: 12.06.12
%      Author: lasha.abzianidze{at}gmail.com 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- ensure_loaded(['my_word_net']).

:- multifile is_/2.
:- discontiguous is_/2.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%           	ISA Network
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
ext( man,
	[['john'],['sam']] ).
ext( woman,
	[['mary'],['kate'], ['emily'], ['ann']] ).
	
% instance
instance(Instance, Concept) :-
	inst(Instance, Concept),
	!.	
	
instance(Instance, Concept) :-
	inst(Instance, SpecificConcept),
	isa(SpecificConcept, Concept).	

inst(Inst, Concept) :-
	is_list(Inst), % Concept may be Variable (for transitive serach), but nor Inst
	ext(Concept, Extension),
	member(El, Extension),
	match_lowerCase(El, Inst).

% not instance
not_instance(Inst, Concept) :-
	inst(Inst, Inst_Concept),
	disjoint(Inst_Concept, Concept). 

% disjoint
disjoint(A, B) :-
	disjoint_sym(A, B).

disjoint(A, B) :-
	isa(A, A1),
	disjoint_sym(A1, B).

disjoint(A, B) :-
	isa(B, B1),
	disjoint_sym(A, B1).

disjoint(A, B) :-
	isa(A, A1),
	isa(B, B1),
	disjoint_sym(A1, B1).
	
disjoint_sym(A, B) :-
	( disjoint_(A, B)
    ; disjoint_(B, A)
	), !.

% simplification
/*disjoint(A, B) :-
	\+isa(A, B),
	\+isa(B, A).
*/
disjoint_(delegate, survey).
disjoint_(delegate, result).
disjoint_(book, person).
disjoint_(book, person).

disjoint_(A, B) :-
	dis_wn(A, B).

%special classes, all semses should be under them
disjoint_('physical entity', 'abstract entity').
%disjoint_(survey, result).
/*
disjoint_(A, B) :- 
	A \= B,
	disjoint_list(List),
	memberchk(A, List),
	memberchk(B, List), 
	!,
	%\+isa(A, B),
	%\+isa(B, A).
	( (isa(A, B); isa(B,A)) -> report(['Error: ', A, ' and ', B, ' are in isa and disjoint rels']); true ). 
*/

is_(lark, bird).
is_(hound, dog).
is_(dog, animal).
is_(cat, animal).
is_(student, person).
is_(bachelor, man).
is_(man, person).
is_(woman, person).
is_(person, human).
is_(human, person).
is_(european, person). %!!!

is_(fly, hover).
is_(hover, move).
is_(walk, move).
is_(run, move).
is_(obtain, receive).
is_(receive, obtain).
is_(build, finish).

is_(every, most). %!!!
is_(most, a).
is_(both, a).
is_(several, a).
is_(many, a).
is_(s, a).
is_(the, a).
is_(a, the).
is_(s, a_few). %!!! wrong
is_(a_few, s).
is_(s, both). %!!! due to generic reading
is_('CD', a). %!!!
is_(one, a).
is_(a, one). %!!! no arithemtic still
is_(two, one).
is_(two, a).
is_(three, two).

is_(kiss, touch).
is_(snore, sleep).
is_('girl', 'young woman'). %sick-303
is_('young woman', 'girl').
is_('polish', 'clean'). %sick-1909
is_('trek', 'hike'). %sick-3182
%is_('dash', 'jump'). %sick-3728 actually neutral
is_('jump', 'bounce'). %sick-4127 in wn mistake 'bound'
is_('dive', 'jump'). %sick-8039
is_('run', 'sprint'). %sick-8532
is_('look', 'stare'). %sick-3750, noise problem

%is_(climb, climb_up). %sick-4006, 4011
%is_(climb_up, climb). %sick-4006, 4011

%is_(play, practice). %sick-3586 but 2842
%is_(practice, play). %sick-3586 but 2842

is_(note, paper). %sick-4360 needs, not found in wordnet
is_(fit, apply).  %sick-4734 needs, not found in wordnet
is_(food, meal).  %sick-5110 needs, not found in wordnet
is_(ringer, wrestler). %sick-5113
is_(wrestler, ringer). %sick-5113
is_(pour, put). %sick-5938
is_(vegetable, ingredient). %sick-5938
is_(lunge, jump). %sick-7795
%is_(lady, girl). %sick-8163, sick-1643 but sick-2027
is_(big, huge). %sick-9359
is_(huge, big). 
is_(elder, elderly). %sick-9571
is_(elderly, elder).
is_(woman, lady). %sick-9584
is_(fight, match). %sick-44
%is_(hat, haeddress). %sick-240
is_(group, crowd). %sick-311
is_(crowd, group). %sick-311


isa(A, B) :-  % variant, not matching
	A =@= B,
	A = B.

isa(A, B) :-
	is_(A, B),
	!.
/*
isa(A, B) :-
	reset_isa_path,
	isa_(A, B).
*/

% Using WordNet dynamic relation
isa(W1, W2) :- 
	isa_wn(W1, W2).



isa_(A, B) :- % variant, not matching
	A =@= B,
	A = B.

isa_(A, C) :- 
	%nonvar(A), nonvar(C), 
	is_(A, B), 
	add_to_isa_path(B), 
	isa_(B, C).


	

:- dynamic isa_path/1.
isa_path([]).

add_to_isa_path(X) :-
	isa_path(Path),
	\+ member(X, Path),
	retract(isa_path(_)),
	NewPath = [X | Path], 
	asserta(isa_path(NewPath)).
	
reset_isa_path :-
	retract(isa_path(_)),
	asserta(isa_path([])).	







