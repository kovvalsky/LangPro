%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- module(ccg_term, [
	ccgIDTree_to_ccgIDTerm/2,
	ccgTree_to_ccgTerm/2,
	dirCat_to_undirCat/2,
	op(601, xfx, (/)),
	op(601, xfx, (\))
]).
%==================================
:- use_module('../lambda/lambda_tt', [
	norm_tt/2, op(605, xfy, ~>), op(605, yfx, @)
	]).	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ccgIDTree_to_ccgIDTerm(CCG_ID, Term_ID)
% Converts (ID, CCGTree) pair into (ID, CCGterm) pair
ccgIDTree_to_ccgIDTerm(ccg(Id, Tree), ccg(Id, NormTT)) :-
	ccgTree_to_ccgTerm(Tree, TT), norm_tt(TT, NormTT).
	%ccgTree_to_ccgTerm(Tree, TT), norm_tt(TT, NormTT), (TT = NormTT -> true; report(['!!! Beta reduction happened'])).
	%ccgTree_to_ccgTerm(Tree, NormTT).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ccgTree_to_ccgTerm(Tree, tcTree))
% Converts CCG Tree into CCG term tcTree (a pair of term and category)
ccgTree_to_ccgTerm(Tree, (Term, UndirCat)) :-
	Tree = t(Cat, Token, Lemma, POS, Feat1, Feat2) -> %add two extra features
		dirCat_to_undirCat(Cat, UndirCat),
		%ccgCat_semType(UndirCat, SemType),					% for sem vs syn types
		%write(SemType), write('\t'), write(UndirCat), nl,	% for sem vs syn types
		downcase_atom(Lemma, LowerCase),
		Term = tlp(Token, LowerCase, POS, Feat1, Feat2);
	Tree = lx(Cat, _, A) ->
		ccgTree_to_ccgTerm(A, TC),
		dirCat_to_undirCat(Cat, UndirCat),
		Term = TC;
		%write(Tree), write('\m');% temp
	( Tree = tr(Cat, A)
	; (Tree = tr(Cat, _, A)) )  ->  % second for easyCCG output
		dirCat_to_undirCat(Cat, UndirCat),
		UndirCat = (CatArg ~> CatVal) ~> CatVal,
		ccgTree_to_ccgTerm(A, TC),
		TC_X = (_, CatArg ~> CatVal),
		Term = abst(TC_X, (TC_X @ TC, CatVal));
	(Tree = fa(Cat, A, B);
	 Tree = ba(Cat, B, A))  ->
		dirCat_to_undirCat(Cat, UndirCat),
		ccgTree_to_ccgTerm(A, TC_A),
		ccgTree_to_ccgTerm(B, TC_B),
		Term = TC_A @ TC_B;
	(Tree =  fc(Cat, A, B);
	 Tree =  bc(Cat, B, A);
	 Tree = fxc(Cat, A, B);
	 Tree = bxc(Cat, B, A)) ->
		dirCat_to_undirCat(Cat, UndirCat),
		UndirCat = Cat_X ~> Cat_Val,
		ccgTree_to_ccgTerm(A, TC_A),
		ccgTree_to_ccgTerm(B, TC_B),
		TC_B = (_, Cat_X ~> Cat_Val_B),
		TC_X = (_, Cat_X),
		Term = abst(TC_X, (TC_A @ (TC_B @ TC_X, Cat_Val_B), Cat_Val));
	Tree = conj(Cat, Arg, A, B) ->
		dirCat_to_undirCat(Cat, UndirCat),
		dirCat_to_undirCat(Arg, UndirArg),
		UndirCat = UndirArg ~> UndirArg,
		ccgTree_to_ccgTerm(A, (TA, _CA)),
		ccgTree_to_ccgTerm(B, TC_B),
		TC_A = (TA, UndirArg~>UndirArg~>UndirArg),
		TC_B = (_TB, UndirArg),
		%term_to_atom(CA, Atom), writeln(Atom),
		%term_to_atom(UndirCatArg, Atom1), writeln(Atom1),
		%term_to_atom(CB, Atom2), writeln(Atom2),
		Term = TC_A @ TC_B;
	(Tree = lp(Cat, _, A);
	 Tree = rp(Cat, A, _)) ->
		dirCat_to_undirCat(Cat, UndirCat),
		%B = t(_, _, _, P, _, _),
		%once(member(P, [':','.',',','"', '#','$','`','(',')','\'', 'LQU', 'RQU'])),
		ccgTree_to_ccgTerm(A, (Term, UndirCat));
	(Tree = ltc(Cat, _, A);
	 Tree = rtc(Cat, A, _)) ->
		dirCat_to_undirCat(Cat, UndirCat),
		ccgTree_to_ccgTerm(A, TC_A),
		Term = TC_A;
	(Tree = gbxc(Cat, 2, A, B);  Tree = gbc(Cat, 2, A, B);
     Tree = gbxc(Cat, A, B);     Tree = gbc(Cat, A, B);
	 Tree = gfxc(Cat, 2, B, A);  Tree = gfc(Cat, 2, B, A);
     Tree = gfxc(Cat, B, A);     Tree = gfc(Cat, B, A) ) ->
		dirCat_to_undirCat(Cat, UndirCat),
		ccgTree_to_ccgTerm(A, TC_A),
		ccgTree_to_ccgTerm(B, TC_B),
		TC_A = (_, Cat_X ~> Cat_Y ~> Cat_Val_A),
		UndirCat = Cat_X ~> Cat_Y ~> Cat_Val,
		TC_X = (_, Cat_X),
		TC_Y = (_, Cat_Y),
		Term = abst(TC_X, (abst(TC_Y, (TC_B @ ((TC_A @ TC_X, Cat_Y ~> Cat_Val_A) @ TC_Y, Cat_Val_A), Cat_Val)), Cat_Y ~> Cat_Val));
	Tree =.. [Comb | _],
	format('Error in getting CCGterms: ~w', [Comb]).
	%write(Id).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% dirCat_to_undirCat(DirCat, UndirCat)
% Converts (directed) Syntactic category DirCat into undirected UndirCat
dirCat_to_undirCat(DirCat, UndirCat) :-
	nonvar(DirCat),
	(DirCat = A/B; DirCat = A\B), !,
	dirCat_to_undirCat(A, UndirA),
	dirCat_to_undirCat(B, UndirB),
	UndirCat = UndirB ~> UndirA.

dirCat_to_undirCat(DirCat, UndirCat) :-
	nonvar(DirCat),
	((DirCat = s; DirCat = n; DirCat = np) ->
		UndirCat = DirCat : _Feat;
	 UndirCat = DirCat ).
