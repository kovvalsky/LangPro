%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- module('correct_term',
	[
		correct_ccgTerm/2
	]).

:- use_module('ccgTerm_to_llf', [ccgTerm_to_llf/2]).
:- use_module('../lambda/lambda_tt', [op(605, yfx, @), op(605, xfy, ~>)]).
:- use_module('../lambda/type_hierarchy', [cat_eq/2]).

:- dynamic debMode/1.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
correct_ccgTerm(Term, SimCorrTerm) :-
	ccgTerm_to_llf(Term, CorrTerm),
	simplify(CorrTerm, SimCorrTerm).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% replace some -> a, every -> all
% plural to singular

simplify((Var, Type), (Var, Type)) :-
	var(Var), !.

simplify((TT1 @ TT2, Type), (SimTT1 @ SimTT2, Type)) :-
	!, simplify(TT1, SimTT1),
	simplify(TT2, SimTT2).

simplify( (abst(TTx, TT), Type), (abst(TTx, SimTT), Type) ) :-
	!, simplify(TT, SimTT).

% treats all constant:np as constant:e
%simplify( (tlp(Tk,Lem,Pos,F1,F2), np:X),  SimTT) :-
%	X \= 'thr',
%	simplify( (tlp(Tk,Lem,Pos,F1,F2), e), SimTT), %e.g. people -> person
%	!.

simplify( (tlp(Off,Lem,'NNS',F1,F2), Type),  SimTT) :-
%simplify( (tlp(_Tk,Lem,'NNS',F1,F2), Type),  (tlp(Lem,Lem,'NN',F1,F2), Type) ) :-
	simplify( (tlp(Off,Lem,'NN',F1,F2), Type), SimTT), %e.g. people -> person
	!.

% substitute possesive pronouns with 'the' sick-240
simplify( (tlp(Off,_Lem,'PRP$',F1,F2), Type),  SimTT) :-
	Type = n:_~>np:_,
	SimTT = (tlp(Off,'the','DT',F1,F2), Type),
	!.

% atomic PPs to atomic PR (simplier solution than changing rules and extractor)
simplify( (tlp(Off,Lm,IN_WDT,F1,F2), pp),  SimTT) :-
	SimTT = (tlp(Off,Lm,IN_WDT,F1,F2), pr),
	!.

% substitute relative that by who %test
simplify( (tlp(Off,'that',IN_WDT,F1,F2), (np:A~>s:B)~>n:C~>n:D),  SimTT) :- % what?
	SimTT = (tlp(Off,'who',IN_WDT,F1,F2), (np:A~>s:B)~>n:C~>n:D), % offset mismatch
	!.

simplify( (tlp(Off,Lem,Pos,F1,F2), Type), (tlp(Off,Lemma,Pos,F1,F2), Type) ) :-
	!,
	( Lem = 'none', Lemma = 'no';
	  debMode('noPl'), Lem = 's' ->
		Lemma = 'a'
	; debMode('noHOQ'), member(Lem, ['most','many','several','a_few','both']) ->
		Lemma = 'a'
	; debMode('noThe'), Lem = 'the' ->
		Lemma = 'a'
	; debMode('a2the'), memberchk(Lem, ['a', 'an']) ->
		Lemma = 'the'
	; debMode('s2the'), Lem = 's' ->
		Lemma = 'the'
	; Lem = 'which', Lemma = 'who'; % what about tokens? why dont u change them? another use for which? non vp,n,n type?
	  Lem = 'some',Lemma = 'a';
	  Lem = 'an',  Lemma = 'a';
	  Lem = 'all', Lemma = 'every'; % all cake =\= each cake
	  Lem = 'each', Lemma = 'every';
	  Lem = 'a_lot_of', Lemma = 'many';
	  Lem = 'neither', Lemma = 'no'; % fracas-46, but neither has a presupposition
	  Lem = 'people', Lemma = 'person';
	  Lem = 'n\'t', Lemma = 'not';
	  %Lem = 'the', Lemma = 'a'; %what about the dogs? % the concert means only one concert in the branch
	  %Lem = 's', Lemma = 'a';	% ignore plurals
	  Lemma = Lem
	), !.

simplify( (TT, Type), (SimTT, Type) ) :-
	!, simplify(TT, SimTT).
