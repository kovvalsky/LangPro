%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Recognizing named entities
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- module('ner',
	[
		ne_ccg/2
	]).

:- use_module('../printer/reporting', [report/1]).
:- use_module('../utils/user_preds', [off2tag/4, off2anno/3]).
:- use_module('../llf/ccg_term', [ccgIDTree_to_ccgIDTerm/3]).
:- use_module('../lambda/lambda_tt', [op(605, yfx, @)]).

test_ne :-
	forall(ccg(Id,_), test_ne(Id)).

test_ne(ID) :-
	( sen_id_to_base_ttterm(ID, Tree),
	  ne_ccg(Tree, _)
	-> true
	; once(sen_id(ID,_,_,_,_,Sen)),
	  format('~w: failed ne_ccg (~w)~n', [ID, Sen]) ).
	%atomic_list_concat(['=====', ID, '====='],Message), writeln(Message).

ne_ccg(T, T_ne) :-
	ne_search(T, T_ne, _).


% TO THINK: ignore annotatiosn from ne_search?
ne_search((X, Cat), (X, Cat), _) :-
	var(X), !.

ne_search((Exp, Cat), (Exp_ne, Cat), POS) :-
	Exp = TC1 @ TC2, !,
	ne_search(TC1, TC1_ne, POS1),
	ne_search(TC2, TC2_ne, POS2),
	( POS1 == POS2 -> % i.e. both are non-var
		TC1_ne = (tlp(O1,L1,_,_,N1), _),
		TC2_ne = (tlp(O2,L2,_,_,N2), _),
		atomic_list_concat([L1,'_',L2], L),
		append(O1, O2, O),
		( N1 == 'O' -> N = N2; N = N1 ),
		Exp_ne = tlp(O,L,POS1,'0',N),
		POS = POS1,
		( debMode('ne') -> report(['!!! complex NE found: ', POS, ' ', L]); true )
	; Exp_ne = TC1_ne @ TC2_ne % POS becomes unbound
	).

ne_search((TLP, Cat), (TLP, Cat), POS1) :-
	TLP = tlp(_,_,POS,_,N), !,
	(atom_chars(POS, ['N','N','P'|_]) ->
		POS1 = 'NNP';
	 atom_chars(POS, ['J','J'|_]), N = 'I-ORG' ->  % North JJ American JJ I-ORG (fracas 67 prob)
		POS1 = 'JJ';
	true). % POS1 becomes unbound

ne_search((Exp, Cat), (Exp_ne, Cat), _) :-
	Exp = (_, _), !,
	ne_search(Exp, Exp_ne, _).

ne_search((Exp,Cat), (abst(X,TC_ne), Cat), _) :-
	Exp = abst(X, TC), !,
	ne_search(TC, TC_ne, _).
