%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- module(ccg_term, [
	ccgIDTree_to_ccgIDTerm/2,
	ccgIDTree_to_ccgIDTerm/3,
	ccgTree_to_ccgTerm/3,
	dirCat_to_undirCat/2,
	op(601, xfx, (/)),
	op(601, xfx, (\))
]).
%==================================
:- use_module('../lambda/lambda_tt', [
	norm_tt/2, op(605, xfy, ~>), op(605, yfx, @)
	]).
:- use_module('../utils/user_preds', [sen_id2anno/3]).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ccgIDTree_to_ccgIDTerm(CCG_ID, Term_ID)
% Converts (ID, CCGTree) pair into (ID, CCGterm) pair
ccgIDTree_to_ccgIDTerm(Id_Tree, ccg(Id, NormTT)) :-
	( Id_Tree = ccg(Id, Tree) -> true
	; number(Id_Tree), Id = Id_Tree ), 
	ignore(sen_id2anno(Id, Tree, Anno)), % to be comaptible with old-style
	ccgIDTree_to_ccgIDTerm(ccg(Id, Tree), ccg(Id, NormTT), Anno).

ccgIDTree_to_ccgIDTerm(ccg(Id, Tree), ccg(Id, NormTT), Annos) :-
	ccgTree_to_ccgTerm(Tree, TT, Annos),
	norm_tt(TT, NormTT).
	%ccgTree_to_ccgTerm(Tree, TT), norm_tt(TT, NormTT), (TT = NormTT -> true; report(['!!! Beta reduction happened'])).
	%ccgTree_to_ccgTerm(Tree, NormTT).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ccgTree_to_ccgTerm(Tree, tcTree))
% Converts CCG Tree into CCG term tcTree (a pair of term and category)
% Annos needs to be disambiguated so that each annotation level has a singel value
ccgTree_to_ccgTerm(Tree, (Term, UndirCat), Annos) :-
	Tree = t(Cat, Token, Lemma, POS, I, N) -> %add two extra features
		dirCat_to_undirCat(Cat, UndirCat),
		%ccgCat_semType(UndirCat, SemType),					% for sem vs syn types
		%write(SemType), write('\t'), write(UndirCat), nl,	% for sem vs syn types
		downcase_atom(Lemma, LowerCase),
		Term = tlp(Token, LowerCase, POS, I, N);
	Tree = t(Cat, Token, Offset) ->
		member(TokA, Annos),
		[Offset] == TokA.o, % ccg term ofsets are X-Y, not list
		Token == TokA.t, !,
		dirCat_to_undirCat(Cat, UndirCat),
		Term = tlp(TokA.o, TokA.l, TokA.ppos, '0', TokA.ner);
	( Tree = lx(Cat, _, A)
	; Tree = lex(Cat, _, A) ) ->
		ccgTree_to_ccgTerm(A, TC, Annos),
		dirCat_to_undirCat(Cat, UndirCat),
		Term = TC;
		%write(Tree), write('\m');% temp
	( Tree = tr(Cat, A)
	; Tree = tr(Cat, _, A) )  ->  % second for easyCCG output
		dirCat_to_undirCat(Cat, UndirCat),
		UndirCat = (CatArg ~> CatVal) ~> CatVal,
		ccgTree_to_ccgTerm(A, TC, Annos),
		TC_X = (_, CatArg ~> CatVal),
		Term = abst(TC_X, (TC_X @ TC, CatVal));
	( Tree = fa(Cat, A, B)
	; Tree = ba(Cat, B, A) )  ->
		dirCat_to_undirCat(Cat, UndirCat),
		ccgTree_to_ccgTerm(A, TC_A, Annos),
		ccgTree_to_ccgTerm(B, TC_B, Annos),
		Term = TC_A @ TC_B;
	(Tree =  fc(Cat, A, B)
	; Tree =  bc(Cat, B, A)
	; Tree = fxc(Cat, A, B); Tree = fx(Cat, A, B)
	; Tree = bxc(Cat, B, A); Tree = bx(Cat, B, A) ) ->
		dirCat_to_undirCat(Cat, UndirCat),
		UndirCat = Cat_X ~> Cat_Val,
		ccgTree_to_ccgTerm(A, TC_A, Annos),
		ccgTree_to_ccgTerm(B, TC_B, Annos),
		TC_B = (_, Cat_X ~> Cat_Val_B),
		TC_X = (_, Cat_X),
		Term = abst(TC_X, (TC_A @ (TC_B @ TC_X, Cat_Val_B), Cat_Val));
	Tree = conj(Cat, Arg, A, B) ->
		(Cat = Arg\Arg -> true; format('Wrong conj: conj(~w, ~w~n', [Cat, Arg])),
		dirCat_to_undirCat(Cat, UndirCat),
		dirCat_to_undirCat(Arg, UndirArg),
		UndirCat = UndirArg ~> UndirArg,
		ccgTree_to_ccgTerm(A, (TA, _CA), Annos),
		ccgTree_to_ccgTerm(B, TC_B, Annos),
		TC_A = (TA, UndirArg~>UndirArg~>UndirArg),
		TC_B = (_TB, UndirArg),
		%term_to_atom(CA, Atom), writeln(Atom),
		%term_to_atom(UndirCatArg, Atom1), writeln(Atom1),
		%term_to_atom(CB, Atom2), writeln(Atom2),
		Term = TC_A @ TC_B;
	( Tree = lp(Cat, P, A)
	; Tree = rp(Cat, A, P) ) ->
		dirCat_to_undirCat(Cat, UndirCat),
		%B = t(_, _, _, P, _, _),
		%once(member(P, [':','.',',','"', '#','$','`','(',')','\'', 'LQU', 'RQU'])),
		ccgTree_to_ccgTerm(A, (Term1, UndirCat1), Annos),
		( UndirCat1 = UndirCat ->
			Term = Term1 % punctuation can be omitted as it acts as identity term
		; P =.. ['t', _PunctCat | TLPCN ],
		  TP =.. ['t', UndirCat1~>UndirCat | TLPCN ],
		  ccgTree_to_ccgTerm(TP, TP_C, Annos),
		  Term = TP_C @ (Term1, UndirCat1)
		);
	( Tree = ltc(Cat, _, A)
	; Tree = rtc(Cat, A, _) ) ->
		dirCat_to_undirCat(Cat, UndirCat),
		ccgTree_to_ccgTerm(A, TC_A, Annos),
		Term = TC_A;
	( Tree = gbxc(Cat, 2, A, B);  Tree = gbc(Cat, 2, A, B)
    ; Tree = gbxc(Cat, A, B);     Tree = gbc(Cat, A, B)
	; Tree = gfxc(Cat, 2, B, A);  Tree = gfc(Cat, 2, B, A)
    ; Tree = gfxc(Cat, B, A);     Tree = gfc(Cat, B, A) ) ->
		dirCat_to_undirCat(Cat, UndirCat),
		ccgTree_to_ccgTerm(A, TC_A, Annos),
		ccgTree_to_ccgTerm(B, TC_B, Annos),
		TC_A = (_, Cat_X ~> Cat_Y ~> Cat_Val_A),
		UndirCat = Cat_X ~> Cat_Y ~> Cat_Val,
		TC_X = (_, Cat_X),
		TC_Y = (_, Cat_Y),
		Term = abst(TC_X, (abst(TC_Y, (TC_B @ ((TC_A @ TC_X, Cat_Y ~> Cat_Val_A) @ TC_Y, Cat_Val_A), Cat_Val)), Cat_Y ~> Cat_Val));
	Tree =.. [Comb | _], % !!! fail?
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
