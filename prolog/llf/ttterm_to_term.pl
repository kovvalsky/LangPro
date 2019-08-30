%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- module('ttterm_to_term',
	[
		ttTerm_to_prettyTerm/2,
		ttTerm_to_norm_term/5,
		ttTermList_to_prettyTermList/2,
		type_to_prettyType/2
	]).

:- use_module('../utils/user_preds', [true_member/2]).
:- use_module('../knowledge/lexicon', [op(640, xfy, ::)]).
:- use_module('../lambda/lambda_tt', [op(605, yfx, @), op(605, xfy, ~>)]).	
:- use_module('../lambda/lambda', [betaEtaNorm/2]).	

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




	
ttTermList_to_prettyTermList([TT_H | TT_Rest], [H | Rest]) :-
	ttTerm_to_prettyTerm(TT_H, H),
	ttTermList_to_prettyTermList(TT_Rest, Rest).

ttTermList_to_prettyTermList([], []).	


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% TTterm or TCterm expression to lambda term
%ttTerm_to_prettyTerm(AtomTT, Atom) :-
%	var(AtomTT),
%	!,
%	fail.

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
% Type to prettyType
type_to_prettyType(A, A) :-
	(atom(A); var(A)), 
	!.

type_to_prettyType(A:F, A1) :-
	( atom(F) -> 
	  	A1 = A:F
	  ;	A = A1
	), !.

type_to_prettyType(A~>B, A1~>B1) :-
	nonvar(A),
	nonvar(B), !,
	type_to_prettyType(A, A1),
	type_to_prettyType(B, B1).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Term to pretty_ttTerm
ttTerm_to_pretty_ttTerm(AtomTT, (Atom, PPtype)) :-
	AtomTT =.. [_, Atom, Type],
	atom(Atom),
	type_to_prettyType(Type, PPtype), !.	

ttTerm_to_pretty_ttTerm(AtomTT, (Atom, PPtype)) :-
	AtomTT =.. [_, tlp(_,Atom,_,_,_), Type],
	type_to_prettyType(Type, PPtype), !.
	
ttTerm_to_pretty_ttTerm(VarTT, (Var, PPtype)) :-
	VarTT =.. [_, Var, Type],
	var(Var), 
    type_to_prettyType(Type, PPtype), !.
	%term_to_atom(Var,AtomVar),
	%atom_chars(AtomVar, [_,_|Index])
	 
ttTerm_to_pretty_ttTerm(AppTT, PPterm1 @ PPterm2) :-
	AppTT =.. [_, TTterm1 @ TTterm2, _Type], !,
	%type_to_prettyType(Type, PPtype),
	ttTerm_to_pretty_ttTerm(TTterm1, PPterm1),
	ttTerm_to_pretty_ttTerm(TTterm2, PPterm2).
	
ttTerm_to_pretty_ttTerm(AbstTT, abst(PPvar, PPttTerm)) :-
	AbstTT =.. [_, abst(TTvar, TT), _Type], !,
	%type_to_prettyType(Type, PPtype),
	ttTerm_to_pretty_ttTerm(TTvar, PPvar),
	ttTerm_to_pretty_ttTerm(TT, PPttTerm).



