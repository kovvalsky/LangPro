%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Description: Knowledge Base
%     Version: 12.06.12
%      Author: lasha.abzianidze{at}gmail.com
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- module(knowledge,
	[
		disjoint/3,
		word_synonyms/3,
		isa/3,
		ant_wn/3,
		derive/3,
		instance/3,
		not_instance/3,
		not_disjoint/3,
		not_isa/3,
		positional_isa/3
	]).

:- multifile is_/2.
:- discontiguous is_/2.

:- ensure_loaded([
	'my_word_net'
	]).

:- use_module('disjoint', [disj_/2]).
:- use_module('../utils/user_preds', [match_lowerCase/2, is_uList/1, ul_member/2]).
:- use_module('../printer/reporting', [report/1]).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%           	ISA Network
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
ext( man,
	[['john'],['sam']] ).
ext( woman,
	[['mary'],['kate'], ['emily'], ['ann']] ).

% instance
instance(Instance, Concept, _KB-XP) :-
	inst(Instance, Concept),
	!,
	ul_append(XP, [ins(Instance, Concept)]).

instance(Instance, Concept, KB-XP) :-
	inst(Instance, SpecificConcept),
	isa(SpecificConcept, Concept, KB-XP), %CHECK
	ul_append(XP, [ins(Instance, Concept)]).

inst(_Inst, _Concept) :-
	debMode('no_kb'),
	!, fail.

inst(Inst, Concept) :-
	is_list(Inst), % Concept may be Variable (for transitive serach), but nor Inst
	ext(Concept, Extension),
	member(El, Extension),
	match_lowerCase(El, Inst).

% not instance
not_instance(Inst, Concept, KB-XP) :-
	inst(Inst, Inst_Concept),
	disjoint(Inst_Concept, Concept, KB-XP),
	ul_append(XP, [ins(Inst, Inst_Concept)]).


ant_wn(A, B, KB-XP) :-
	memberchk(ant_wn(A, B), KB),
	ul_append(XP, [ant(A, B)]).


% capyures deriavtional morphology
derive(A, B, KB-XP) :-
	memberchk(der_wn(A, B), KB),
	ul_append(XP, [der(A,B)]).


% disjoint based on KB
disjoint(A, B, KB-XP) :-
	once(( 	memberchk(disj(A, B), KB)
		;	memberchk(disj(B, A), KB)
		; 	disjoint(A, B)
		)),
	ul_append(XP, [dis(A,B)]).

not_disjoint(A, B, KB-_XP) :- %FIXME specify non disjointness
	\+ul_member(disj(A, B), KB),
	\+ul_member(disj(A, B), KB),
	\+disjoint(A, B).

% disjoint
disjoint(_, _) :-
	debMode('no_kb'),
	!, fail.

disjoint(A, B) :-
	disjoint_sym(A, B).
/* allows weird contradictions: e.g. card trick is person, person disj trick therfore disj
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
*/
disjoint_sym(A, B) :-
	( disjoint_(A, B)
	; disjoint_(B, A)
	; (debMode('disj') ->  ( disj_(A, B) ; disj_(B, A) ); false )
	), !.

% simplification
/*disjoint(A, B) :-
	\+isa(A, B),
	\+isa(B, A).
*/
%disj_(woman, man).

disjoint_(delegate, survey).
disjoint_(delegate, result).
disjoint_(book, person).
disjoint_(book, person).
disjoint_(contract, chairman).



%special classes, all semses should be under them
disjoint_('physical entity', 'abstract entity').
%disjoint_(survey, result).


disjoint_(A, B, KB) :-
	memberchk(dis_wn(A, B), KB).
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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% is_/2 direct isa relation, atomic facts
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

is_(win, won). %fracas-49 for eccg
is_(won, win).

is_(kiss, touch).
is_(snore, sleep).
is_('girl', 'young woman'). %
is_('young woman', 'girl'). % sick-7606, 303, 1988,
is_('boy', 'young man'). %sick-5781
is_('young man', 'boy').
is_('polish', 'clean'). %sick-1909
%is_('trek', 'hike'). %sick-3182 slow trek->hike, but not 3181
%is_('dash', 'jump'). %sick-3728 actually neutral
is_('jump', 'bounce'). %sick-4127 in wn mistake 'bound'
is_('dive', 'jump'). %sick-8039
is_('run', 'sprint'). %sick-8532
is_('look', 'stare'). %sick-3750, noise problem
is_('bikini', 'swimming suite'). %sick-8986

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
is_('hole', 'earth').

% frequent pairs
is_(man, person).
is_(lady, woman).
is_(woman, person).
is_(woman, lady).
is_(child, person).
is_(snowboarder, person).
is_(skateboarder, person).
is_(keyboard, piano).
is_(rider, person).
is_(lady, person).
is_(cliff, rock).
is_(rock, cliff).
is_(child, kid).
is_(kid, child).
is_(wave, water).
is_(road, street).
is_(street, road).
is_(practitioner, trainer).
is_(trainer, practitioner).
is_(bicycle, bike).
is_(bike, bicycle).
is_(person, animal).
is_(dog, animal).
is_(girl, person).
is_(boy, person).
is_(ocean, water).
is_(cowboy, man).
is_(lake, water).
is_(player, person).
is_(grass, lawn).
is_(lawn, grass).
is_(car, vehicle).
is_(whisk, wire).
is_(fountain, water).
%is_(cyclist, person). % sick-8606
is_(sheet, paper).  %sick-5264 deosnt like
%is_(paper, sheet). %sick-4363 doesnt like

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Knowledge about quantifiers
isq_(every, most). %!!!
isq_(most, a).
isq_(both, a).
isq_(s, most). %fracas 100
isq_(several, a).
isq_(many, a).
isq_(s, a).
isq_(the, a).
isq_(a, the).
isq_(s, a_few). %!!! wrong
isq_(a_few, s).
isq_(s, both). %!!! due to generic reading, 13, wrong
isq_('CD', a). %!!!
isq_(one, a).
isq_(a, one). %!!! no arithemtic still
%is_(two, one). % wrong for fracas 287
isq_(two, a).
isq_(three, two).


% for player vs play, Sick-107
isa(A, B, _KB-XP) :-
	atom(A), atom(B),
	( 	atom_concat(A, 'er', B),
		R = der(A, B)
 	;  	atom_concat(B, 'er', A),
		R = der(B, A)
	), !,
	ul_append(XP, [R]).

isa(A, B, _KB_XP) :-  % variant, not matching
	A =@= B, !.

isa(A, B, _KB_XP) :-
	( ( debMode('no_kb') -> false; is_(A, B) )
	; ( debMode('no_qk') -> false; isq_(A, B) )
	), !.

% KB without assertions
isa(W1, W2, KB-XP) :- % CHECK
	\+is_uList(KB), !,
	( 	memberchk(isa_wn(W1, W2), KB),
	  	ul_append(XP, [isa(W1, W2)])
	; 	memberchk(sim_wn(W1, W2), KB),
		ul_append(XP, [sim(W1, W2)])
	), !.

isa(W1, W2, KB_-XP) :-
	is_uList(KB_),
	memberchk(isa_wn(W1, W2), KB_),
	ul_append(XP, [isa(W1, W2)]).

not_isa(A, B, KB-_XP) :- %FIXME specify negative info
	\+ul_member(isa_wn(A, B), KB).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% checks if two words can have synonymous senses
% based on a KB
word_synonyms(W1, W2, KB-XP) :-
	nonvar(W1),
	nonvar(W2),
	%s(SS, _, W1, _, _, _), 	s(SS, _, W2, _, _, _),
	isa(W1, W2, KB-XP),
	isa(W2, W1, KB-XP), % more efficient
	!.

% doen@op <=> opdoen sicknl-2911
% klimmen@op <=> beklimmen sicknl-4006/11
positional_isa(Pre_V2, V1-PR, KB-XP) :-
	member(P, [PR, 'be', 'ver']),
	atom_concat(P, V2, Pre_V2),
	isa(V2, V1, KB-_XP), !,
	atomic_list_concat([V1,PR], '_', V1_PR),
	ul_append(XP, [isa(V1_PR, Pre_V2)]).

positional_isa(V1-PR, Pre_V2, KB-XP) :-
	member(P, [PR, 'be', 'ver']),
	atom_concat(P, V2, Pre_V2),
	isa(V1, V2, KB-_XP), !,
	atomic_list_concat([V1,PR], '_', V1_PR),
	ul_append(XP, [isa(V1_PR, Pre_V2)]).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Transitivity feature of isa/2 relation
/*
isa(A, B, KB) :-
	nonvar(A) ->
		is_(A, X),
		isa_(X, B);
	nonvar(B) ->
		is_(X, B),
		isa_(A, X).

isa_(X, Y) :-
	( X = Y
    ; X=@=Y ), !.

isa_(X, Y) :-
	nonvar(X) ->
		is_(X, Z),
		isa_(Z, Y);
	nonvar(Y) ->
		is_(Z, Y),
		isa_(X, Z).
*/
