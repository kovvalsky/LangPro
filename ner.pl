%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Recognizing named entities
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

test_ne :-
	forall(ccg(Id,_), test_ne(Id)).

test_ne(ID) :-
	ccg(ID, Tree),
	ccgIDTree_to_ccgIDTerm(ccg(ID, Tree), ccg(ID, Term)),
	ne_search(Term, _, _, _).
	%atomic_list_concat(['=====', ID, '====='],Message), writeln(Message). 

ne_ccg(Term, Term_ne) :-
	ne_search(Term, Term_ne, _, _).



ne_search((Exp, Cat), (Exp_ne, Cat), _, _) :-
	var(Exp), !,
	Exp_ne = Exp.

ne_search((Exp, Cat), (Exp_ne, Cat), Lemma, Flag) :-
	Exp = TC1 @ TC2, !,
	ne_search(TC1, TC1_ne, Lemma1, Flag1),
	ne_search(TC2, TC2_ne, Lemma2, Flag2),
	( Flag1 == Flag2 ->
		atomic_list_concat([Lemma1, '_', Lemma2], Lemma),
		( debMode('ne') -> report(['!!! complex NE found: ', Flag1, ' ', Lemma]); true ),
		Exp_ne = tlp(Lemma, Lemma, Flag1, na, na), % feat1, feat2 info erased
		Flag = Flag1
	; Exp_ne = TC1_ne @ TC2_ne
	).

ne_search((Exp, Cat), (Exp, Cat), Lemma, Flag) :-
	Exp = tlp(_, Lemma, POS, _F1, F2), !,
	(atom_chars(POS, ['N','N','P'|_]) -> 
		Flag = 'NNP';
	 atom_chars(POS, ['J','J'|_]), F2 = 'I-ORG' ->  % North JJ American JJ I-ORG (fracas 67 prob)
		Flag = 'JJ';
	true).

ne_search((Exp, Cat), (Exp_ne, Cat), _, _) :-
	Exp = (_, _), !,
	ne_search(Exp, Exp_ne, _, _).

ne_search((Exp, Cat), (Exp_ne, Cat), _, _) :-
	Exp = abst(X, TC), !,
	ne_search(TC, TC_ne, _, _),
	Exp_ne = abst(X, TC_ne).






