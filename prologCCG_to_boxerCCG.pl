:- op(601, xfx, (/)).
:- op(601, xfx, (\)).

% command
% swipl -f prologCCG_to_boxerCCG.pl -s ../EasyCCG/SICK_train_eccg -g "prolog_to_boxer('ccg_sen/SICK_train_eccg.pl'), halt"



prolog_to_boxer(FileName) :-
	open(FileName, write, S, [encoding(utf8), close_on_abort(true)]),
	%findall(ccg(Id, Pccg), (ccg(Id, Pccg), member(Id,[431,432,433,434])), PrologCCGs),
	findall(ccg(Id, Pccg), ccg(Id, Pccg), PrologCCGs),
	maplist(prologCCG_to_boxerCCG, PrologCCGs, BoxerCCGs),
	write(S, ':- op(601, xfx, (/)).\n:- op(601, xfx, (\\)).\n:- multifile ccg/2, id/2.\n:- discontiguous ccg/2, id/2.\n\n'),
	maplist(print_boxerCCG(S), BoxerCCGs). 

prolog_to_boxer_id(FileName, IDs) :-
	open(FileName, write, S, [encoding(utf8), close_on_abort(true)]),
	%findall(ccg(Id, Pccg), (ccg(Id, Pccg), member(Id,[431,432,433,434])), PrologCCGs),
	findall(ccg(X, Pccg), (member(X, IDs), ccg(X, Pccg)), PrologCCGs),
	maplist(prologCCG_to_boxerCCG, PrologCCGs, BoxerCCGs),
	%set_output(S),
	write(S, ':- op(601, xfx, (/)).\n:- op(601, xfx, (\\)).\n:- multifile ccg/2, id/2.\n:- discontiguous ccg/2, id/2.\n\n'),
	maplist(print_boxerCCG(S), BoxerCCGs).
	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Convert Prolog CCG to Boxer CCG
prologCCG_to_boxerCCG(ccg(ID, Pccg), ccg(ID, Bccg)) :-
	writeln(ID),
	pccg_bccg(ID, Pccg, Bccg),
	!.
	
pccg_bccg(ID, Pccg, Bccg) :-
	Pccg = lf(ID, N, Cat) ->
		w(ID, N, Tk, Lm, Pos, O, NER, Cat),
		Bccg = t(Cat, Tk, Lm, Pos, O, NER);
	( Pccg =.. [C, Cat, P1, P2], 
	  memberchk(C, [fa, ba, rp, fc, bc]) ) ->
		pccg_bccg(ID, P1, B1),
		pccg_bccg(ID, P2, B2),
		Bccg =.. [C, Cat, B1, B2];
	Pccg = tr(_Cat1, Cat, P) ->
		pccg_bccg(ID, P, B),
		Bccg = tr(Cat, B); % type raising for new easyCCG 28aug15
	( Pccg = lx(Cat1, Cat, P), 
	  memberchk( (Cat1,Cat), [ (np, (s:_\np)\((s:_\np)/np)), 
							   (np, s:_/(s:_\np)), 
							   (pp, (s:_\np)\((s:_\np)/pp))
						     ] ) ) ->
		pccg_bccg(ID, P, B),
		Bccg = tr(Cat, B); % type raising
	Pccg = lx(Cat1, Cat, P) ->
		pccg_bccg(ID, P, B),
		Bccg = lx(Cat, Cat1, B);
	Pccg = conj(Cat, P1, P2) ->
		pccg_bccg(ID, P1, B1),
		pccg_bccg(ID, P2, B2),
		B2 =.. [_, Cat1 | _],
		Bccg = conj(Cat, Cat1, B1, B2);
	( Pccg =.. [C, Cat, P1, P2], 
	  memberchk((C, C1), [(fx,fxc), (bx,bxc), (gfc,gfc), (gbc,gbc)]) ) ->
		pccg_bccg(ID, P1, B1),
		pccg_bccg(ID, P2, B2),
		Bccg =.. [C1, Cat, B1, B2];
	term_to_atom(Pccg, Atom),
	writeln(Atom),
	Pccg =.. [C | _],
	write('Error: UNKNOWN COMBINATOR: '), 
	writeln(C).
	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% print a boxer-style CCG in a nice prolog format
print_boxerCCG(S, ccg(ID, CCG)) :- % deals with ID:ind 
	%write_atom_list(S, ['ccg(', ID, ':', Ind]), % deals with ID:ind 
	write_atom_list(S, ['ccg(', ID]), 			
	print_boxerCCG(S, 1, CCG),
	write(S, ').\n\n'). 

print_boxerCCG(S, Tab, CCG) :-
	write(S, ',\n'),
	tab(S, Tab),
	Tab1 is Tab + 1,
	print_split_ccg(CCG, Funct, SubCCGs),
	write(S, Funct), 
	( SubCCGs \= [] -> 
		%write(S, ','),
	  	maplist(print_boxerCCG(S, Tab1), SubCCGs),
	  	write(S,')')
	; true ).	


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% splits a ccg term in two parts, atom & list, for printing
print_split_ccg(CCG, Funct, SubCCGs) :-
	( CCG =.. [Comb, Cat | SubCCGs],
	memberchk(Comb, [fa, ba, rp, fc, bc, fxc, bxc, tr, gfc, gbc]) ) ->
		term_to_atom(Cat, AtCat),
		atomic_list_concat([Comb, '(', AtCat], Funct);
	CCG =.. [t | _] ->
		term_to_atom(CCG, Funct),
		SubCCGs = [];
	( CCG =.. [Comb, Cat1, Cat2 | SubCCGs],
	memberchk(Comb, [lx, conj]) ) ->
		term_to_atom(Cat1, AtCat1),
		term_to_atom(Cat2, AtCat2),
		atomic_list_concat([Comb, '(', AtCat1, ', ', AtCat2], Funct);
	CCG =.. [Comb | _],
	write('Error: print_splitting: '), writeln(Comb).
	
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% writes a list of atoms in Stream
write_atom_list(S, List) :-
	atomic_list_concat(List, Atom),
	write(S, Atom).

/*
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
	Tree = tr(Cat, A) ->
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
	(Tree = gbxc(Cat, 2, A, B);
	 Tree = gfxc(Cat, 2, B, A)) ->
		dirCat_to_undirCat(Cat, UndirCat),
		ccgTree_to_ccgTerm(A, TC_A),
		ccgTree_to_ccgTerm(B, TC_B),
		TC_A = (_, Cat_X ~> Cat_Y ~> Cat_Val_A),
		UndirCat = Cat_X ~> Cat_Y ~> Cat_Val, 
		TC_X = (_, Cat_X),
		TC_Y = (_, Cat_Y),
		Term = abst(TC_X, (abst(TC_Y, (TC_B @ ((TC_A @ TC_X, Cat_Y ~> Cat_Val_A) @ TC_Y, Cat_Val_A), Cat_Val)), Cat_Y ~> Cat_Val));
	write('Error in getting CCGterms\n').
	%write(Id).	 
*/

