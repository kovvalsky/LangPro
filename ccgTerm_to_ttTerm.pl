%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ccgTerms_to_ttTerms(CCGterms, TTterms)
% converts list of CCGterm into list of ttTerm
ccgTerms_to_ttTerms(CCGterms, TTterms) :-
	%length(CCGterms, N),
	%write(N), nl,
	CCGterms = [ccg(Id, CCGterm) | Rest],
	%ignore(ccgTerm_to_ttTerm(CCGterm, TTterm, [])),
	ccgTerm_to_ttTerm(CCGterm, TTterm, []),
	%(var(TTterm) ->  write(Id), write(' No\n');  writeln(Id)),
	TTterms = [ccg(Id, TTterm) | Tail],
	ccgTerms_to_ttTerms(Rest, Tail).
	
ccgTerms_to_ttTerms([], []).




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Converts CCGterm into ttTerm
% such that ttTerm has form of (Term, Type)
% where Term is LLF and Type is its type
ccgTerm_to_ttTerm((X, _), (Term, Type), Env) :-
	var(X),
	!,
	member(Y::Type, Env), 
	X == Y,
	%Type = f(Cat_Y), %type function of Category
	Term = X.


ccgTerm_to_ttTerm(TC, (abst(TT_X, (TTterm, Type)), XType ~> Type), Env) :- %% lambda
	TC = (abst((X,XCat), TC1), _),  % relation between type and Cat yet
	ccgCat_semType_msg(XCat, XType),	
	TT_X = (X, XType),
	!,	
	ccgTerm_to_ttTerm(TC1, (TTterm, Type), [X::XType | Env]). % Xtype in Env


ccgTerm_to_ttTerm((TC1 @ TC2, _), TTterm, Env) :-
	!,
	%TC1 = (Text1, Cat1),
	%TC2 = (Text2, Cat2),
	ccgTerm_to_ttTerm(TC1, TT1, Env),  
	ccgTerm_to_ttTerm(TC2, TT2, Env),
	TT1 = (_, Type1),
	TT2 = (_, Type2),
	TTterm = (Term, Type),
	% when Fun-Arg has proper types  
	(Type1 = Type2 ~> Type -> 
		Term = TT1 @ TT2;
	/*Cat1 = n~>n, !!!
	Type2 = e ->
		Term1 = abst(P, ((_ @ (_ @ (NNP, e), _), _) @ P, _)),
		atom(NNP), atom(Term2),
		atomic_list_concat([NNP, Term2], Term),
		Type = e;  */	
	% Otherwise 
	TTterm = (TT1 @ TT2, clash)).
	%fail).
	% The last case outputs type clash insetad of fail	
% assuming no abst(X, Var_or_Const)



ccgTerm_to_ttTerm(TC, TTterm, _) :-
	TC = (tlp(_, _, _, _, _), _),
	!,
	ccgTerm_to_constTTterm(TC, TTterm).	% backtrack


%tailored for (tc_tlp) -> ttTrem 
ccgTerm_to_ttTerm(TC, TTterm, _) :-
    TC = (Sub_TC, Cat),
	nonvar(Sub_TC),
	Sub_TC = (TLP, Cat0),
	nonvar(TLP),
	TLP = tlp(_,_,_,_,_),
	!,
	ccgTerm_to_constTTterm(Sub_TC, Sub_TTterm),
	((Cat0, Cat) = (n, np) ->
		ccgTerm_to_constTTterm((TLP, np), TTterm);
	 ((Cat0, Cat) = (np~>s:ng,  n~>n);
	  (Cat0, Cat) = (np~>s:pss, n~>n)) ->
		_q = (_,e~>t),	_n = (_,e~>t),
		_x = (_,e),
		TR_x = abst(_q, _q@_x),
		ttExp_to_ttTerm_info( abst(_n, and @ abst(_x, Sub_TTterm @ TR_x @ 'Univ') @ _n) , TTterm, tch);
	write('Ops! a new lx rule: '),
	term_to_atom(Cat0, At_Cat0), term_to_atom(Cat, At_Cat),
	write(At_Cat0), write(' to '), writeln(At_Cat),
	fail
	).



%tailored for tc(tc) -> ttTerm
ccgTerm_to_ttTerm(TC, TTterm, Env) :-
    TC = (Sub_TC, Cat),
	nonvar(Sub_TC),
	Sub_TC = (_, Cat0),
	%!,
	ccgTerm_to_ttTerm(Sub_TC, Sub_TTterm, Env),
	((Cat0, Cat) = (n, np) ->
	  	(Sub_TTterm = (abst(_, (TTterm @ ('Univ',e~>t),_)),_) ->
			true;		
			ttExp_to_ttTerm_info(a @ Sub_TTterm, TTterm, tch));
	 ((Cat0, Cat) = (np~>s:pss, n~>n);    % treat passives correctly
	  (Cat0, Cat) = (np~>s:dcl, n~>n);
	  (Cat0, Cat) = (np~>s:ng, n~>n)) ->
		_q = (_,e~>t),	_n = (_,e~>t),
		_x = (_,e),
		TR_x = abst(_q, _q@_x),
		ttExp_to_ttTerm_info( abst(_n, and @ abst(_x, Sub_TTterm @ TR_x @ 'Univ') @ _n) , TTterm, tch); 
	write('Ops! a new lx rule: '),
	term_to_atom(Cat0, At_Cat0), term_to_atom(Cat, At_Cat),
	write(At_Cat0), write(' to '), writeln(At_Cat),
	fail
	).




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Converts "terminal" CCGterm into typed constant term
% Typing is sound related to Catyegory
ccgTerm_to_constTTterm(TC, TTterm) :-
	TC = (tlp(Token, Lemma, POS, Feat1, Feat2), Cat),
	ccgCat_semType_msg(Cat, Type),
	TTterm = (Term, Type),
	assign_term(Token, Lemma, POS, (Feat1, Feat2), Cat, Type, Term).





%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% category and semantic type compatibility
ccgCat_semType_msg(Cat, Type) :-
	ccgCat_semType(Cat, Type) -> 
		true;
		write('missmatched: '), write(Cat), write(' vs '), write(Type), write('\n'), fail.
	


ccgCat_semType(pp, e~>t).

ccgCat_semType(conj, X~>X~>X).
ccgCat_semType(comma, _). %!!! comma as X~>X~>X ?
ccgCat_semType(period, period). % maybe not necessary???
ccgCat_semType(lqu, lqu).
ccgCat_semType(rqu, rqu).
ccgCat_semType(rrb, rrb).
ccgCat_semType(lrb, lrb).
ccgCat_semType(colon, colon).

ccgCat_semType(s, (e~>t)~>t).
ccgCat_semType(s:_, (e~>t)~>t).

ccgCat_semType(np, (e~>t)~>t).
ccgCat_semType(np:nb, (e~>t)~>t).
ccgCat_semType(np:expl, (e~>t)~>t). % it, use this info
ccgCat_semType(np:thr, (e~>t)~>t). % there, use this info

ccgCat_semType(n, e~>t).
ccgCat_semType(n:num, e~>t).

ccgCat_semType(A~>B, X~>Y) :-
	ccgCat_semType(A, X),
	ccgCat_semType(B, Y).
	



