%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- module('ttterm_to_term',
	[
		ndId_to_pretty_atom/2,
		ttTerm_to_prettyTerm/2,
		ttTerm_to_norm_term/5,
		type_to_prettyType/2,
		ttTerm_to_pretty_ttTerm/2,
		write_pretty_ttTerm/3
	]).

:- use_module('../utils/generic_preds', [true_member/2]).
%:- use_module('../lambda/lambda_tt', [op(605, yfx, @), op(605, xfy, ~>)]).
:- use_module('../lambda/lambda', [betaEtaNorm/2]).

:- op(640, xfy, ::).
:- op(605, xfy, ~>). 	% more than : 600
:- op(605, yfx, @).   	% more than : 600

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
ttTerm_to_norm_term(TTterm, BENorm, Sig, Voc, Ev_Id) :-
	ttTerm_to_Term(TTterm, Lambda_Term, Sig, Voc, Ev_Id),
	%write(' Term,'),
	%(term_to_atom(Lambda_Term, Lambda_Term_Atom), writeln(Lambda_Term_Atom)),
	betaEtaNorm(Lambda_Term, BENorm).
	%(term_to_atom(BENorm, BENorm_Atom), writeln(BENorm_Atom)),



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% TTterm or TCterm to lambda term
ttTerm_to_Term(AtomTT, Atom, Signature, Set_Voc, Last) :-
	ttTerm_to_Term(AtomTT, Atom, Sig, Voc, [], event_id(0, Last)),
	list_to_set(Voc, Set_Voc),
	list_to_set(Sig, Set_Sig),
	subtract(Set_Sig, Set_Voc, Signature). % should be fixed

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% TTterm or TCterm expression to lambda term
ttTerm_to_Term(AtomTT, Atom, Sig, [], _, event_id(Id, I)) :-
	AtomTT =.. [_, Atom, Type],
	atom(Atom),
	!,
	Sig = [Atom :: Type],
	I = Id.

ttTerm_to_Term(VarTT, Term, [], Voc, AbstVars, event_id(Id, I)) :-
	VarTT =.. [_, Var, Type],
	var(Var),
	!,
	(true_member(Var, AbstVars) ->
		Term = Var,
		Voc = [],
		I = Id;
	 %new_event_index(I),
	 I is Id + 1,
	 atomic_list_concat(['e', I], Var),
	 Term = Var,
	 Voc = [Term :: Type]).


ttTerm_to_Term(AppTT, Term1 @ Term2, Sig, Voc, AbstVars, event_id(Id1, Id3)) :-
	AppTT =.. [_, TTterm1 @ TTterm2, _],
	!,
	ttTerm_to_Term(TTterm1, Term1, Sig1, Voc1, AbstVars, event_id(Id1, Id2)),
	ttTerm_to_Term(TTterm2, Term2, Sig2, Voc2, AbstVars, event_id(Id2, Id3)),
	append(Sig1, Sig2, Sig),
	append(Voc1, Voc2, Voc).

ttTerm_to_Term(AbstTT, abst(AppVar, Term), Sig, Voc, AbstVars, Event_Ids) :-
	AbstTT =.. [_, abst(TTvarApp, TT), _],
	!,
	ttvarsApp_to_term_list(TTvarApp, AppVar, List),
	% deals abstractions with structure abst(P1@P2, )
	append(List, AbstVars, NewAbstVars),
	ttTerm_to_Term(TT, Term, Sig, Voc, NewAbstVars, Event_Ids).

ttTerm_to_Term(TT, Term, Sig, Voc, AbstVars, Event_Ids) :-
	TT =.. [_, TTterm, _],
	!,
	ttTerm_to_Term(TTterm, Term, Sig, Voc, AbstVars, Event_Ids).

%ttExp_to_Term(TTexp, TTexp, Lexicon) :-
%	atom(TTexp).

ttvarsApp_to_term_list(TTvarApp, Term, List) :-
	TTvarApp =.. [_, Arg1, Arg2],
	(var(Arg1) ->
		List = [Arg1], %type info not needed
		Term = Arg1;
		Arg1 = (_,_),
		Arg2 = (_, _),
		ttvarsApp_to_term_list(Arg1, Term1, List1),
		ttvarsApp_to_term_list(Arg2, Term2, List2),
		append(List1, List2, List),
		Term = Term1 @ Term2).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% TTterm or TCterm expression to lambda term
% Type information is dropped

ttTerm_to_prettyTerm(AtomTT, Atom) :-
	AtomTT =.. [_, Atom, _],
	atom(Atom), !.

ttTerm_to_prettyTerm(VarTT, Var) :-
	VarTT =.. [_, Var, _],
	var(Var), !.
	%term_to_atom(Var,AtomVar),
	%atom_chars(AtomVar, [_,_|Index])

ttTerm_to_prettyTerm(AtomTT, Atom) :-
	AtomTT =.. [_, tlp(_,Atom,_,_,_), _], !.

ttTerm_to_prettyTerm(AppTT, Term1 @ Term2) :-
	AppTT =.. [_, TTterm1 @ TTterm2, _], !,
	ttTerm_to_prettyTerm(TTterm1, Term1),
	ttTerm_to_prettyTerm(TTterm2, Term2).

ttTerm_to_prettyTerm(AbstTT, abst(Var, Term)) :-
	AbstTT =.. [_, abst(TTvar, TT), _], !,
	ttTerm_to_prettyTerm(TTvar, Var),
	ttTerm_to_prettyTerm(TT, Term).

ttTerm_to_prettyTerm((TT, _), Term) :-
	ttTerm_to_prettyTerm(TT, Term).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Type to prettyType and vice versa
type_to_prettyType(A, A) :-
	var(A), !.

type_to_prettyType(A, A) :-
	atom(A),
	% basic types without features
	memberchk(A, [pp, pr]), !.

type_to_prettyType(A:F, A:F) :-
	atom(F), !.

type_to_prettyType(A:F, A) :-
	atom(A),
	var(F), !.

type_to_prettyType(A~>B, A1~>B1) :-
	type_to_prettyType(A, A1),
	type_to_prettyType(B, B1).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% TT term to lambda term where leaves keep type/annotation info
% predciate is bidirectional
ttTerm_to_pretty_ttTerm(Var, Var) :- % catching unexpacted vars
	var(Var), !,
	format('Untyped variable in ttTerm_to_pretty_ttTerm/2'),
	fail.
% var: from left to right
ttTerm_to_pretty_ttTerm(VarTT, (Var, PPtype)) :-
	nonvar(VarTT), VarTT =.. [_, Var, Type],
	var(Var), !,
	type_to_prettyType(Type, PPtype).
% var: from right to left
ttTerm_to_pretty_ttTerm((Var, Type), (Var, PPtype)) :-
	var(Var), !,
	type_to_prettyType(Type, PPtype).
% atom: from left to right
ttTerm_to_pretty_ttTerm(AtomTT, (Atom, PPtype)) :-
	nonvar(AtomTT), AtomTT =.. [_F, Atom, Type], % _F can be comma or t
	( atom(Atom); integer(Atom) ), !,
	type_to_prettyType(Type, PPtype).
% atom: from right to left
ttTerm_to_pretty_ttTerm((Atom, Type), (Atom, PPtype)) :-
	( atom(Atom); integer(Atom) ), !,
	type_to_prettyType(Type, PPtype).
% lexical with additional features
ttTerm_to_pretty_ttTerm((tlp(T,L,P,F1,F2), Ty), (T:L:P:F1:F2, PPty)) :-
	nonvar(T), !,
	type_to_prettyType(Ty, PPty).
% lexical with token, lemma, POS
ttTerm_to_pretty_ttTerm((tlp(T,L,P), Ty), (T:L:P, PPty)) :-
	nonvar(T), !,
	type_to_prettyType(Ty, PPty).

ttTerm_to_pretty_ttTerm((TT1 @ TT2, Type), PT1 @ PT2) :-
	( nonvar(TT1); nonvar(PT1) ), !,
	ttTerm_to_pretty_ttTerm(TT1, PT1),
	ttTerm_to_pretty_ttTerm(TT2, PT2),
	TT1 = (_, Ty~>Type),
	TT2 = (_, Ty).

ttTerm_to_pretty_ttTerm((abst(TTvar, TT), Ty~>Type), abst(PTvar, PT)) :-
	( nonvar(TTvar); nonvar(PTvar) ), !,
	ttTerm_to_pretty_ttTerm(TTvar, PTvar),
	ttTerm_to_pretty_ttTerm(TT, PT),
	TT = (_, Type),
	TTvar =.. [_, _, Ty].


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Print pretty ttTerm in a readable way
write_pretty_ttTerm(Pre, _I, 'FAIL'-TLG) :-
	!,
	format('~w~p', [Pre, 'FAIL'-TLG]).

write_pretty_ttTerm(Pre, _I, (Var,Ty)) :-
	var(Var), !,
	format('~w(~p, ~p)', [Pre, Var, Ty]).

write_pretty_ttTerm(Pre, _I, (Atom,Ty)) :-
	( atom(Atom); integer(Atom); Atom = _:_ ), !,
	format('~w(~p, ~p)', [Pre, Atom, Ty]).

write_pretty_ttTerm(Pre, I, PTT1 @ PTT2) :-
	!, atomic_concat(I, '  ', I2),
	atomic_concat(Pre, '( ', Pre1),
	write_pretty_ttTerm(Pre1, I2, PTT1),
	atomic_list_concat(['\n', I, '@ '], Pre2),
	write_pretty_ttTerm(Pre2, I2, PTT2),
	write(' )').

write_pretty_ttTerm(Pre, I, abst(Var, PTT)) :-
	!, atomic_concat(I, '      ', I6),
	atomic_concat(Pre, 'abst( ', Pre1),
	write_pretty_ttTerm(Pre1, I6, Var),
	atomic_list_concat([',\n', I, '      '], Pre2),
	write_pretty_ttTerm(Pre2, I6, PTT),
	write(' )').



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
ndId_to_pretty_atom(ndId(Nd, Id), Pretty) :-
	Nd = nd(Mods, TT, Args, TF),
	maplist(ttTerm_to_prettyTerm, Mods, PrettyMods),
	maplist(ttTerm_to_prettyTerm, Args, PrettyArgs),
	ttTerm_to_prettyTerm(TT, PrettyTT),
	% format(atom(Pretty), '~t~w:~5|~t~w~6+ : ~w : ~w : ~w',
	format(atom(Pretty), '~w: ~w : ~w : ~w : ~w',
		[Id, TF, PrettyMods, PrettyTT, PrettyArgs]).
