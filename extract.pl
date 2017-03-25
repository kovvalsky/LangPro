%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Print all lexical rules
print_all_lx_rules :-
	findall(Tree, ccg(_, Tree), CCGTrees),
	maplist(print_lx_rules, CCGTrees).

print_lx_rules(Tree) :- 
	Tree =.. [t | _] ->
		true;
	Tree =.. [lx | _] ->
		term_to_atom(Tree, A_Tree),	
		writeln(A_Tree);
	(Tree =  fa(_, A, B); 
	 Tree =  ba(_, B, A);
	 Tree =  fc(_, A, B);
	 Tree =  bc(_, B, A);
	 Tree = fxc(_, A, B);
	 Tree = bxc(_, B, A);
	 Tree = conj(_, _, A, B);
	 Tree = gbxc(_, 2, A, B);
	 Tree = gfxc(_, 2, B, A))  -> 
		print_lx_rules(A), 
		print_lx_rules(B);
	(Tree = tr(_, A);
	 Tree = lp(_, _, A);
	 Tree = rp(_, A, _);
	 Tree = ltc(_, _, A);
	 Tree = rtc(_, A, _)) ->
		print_lx_rules(A);  
	writeln('ERROR in getting CCGterms').



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
print_used_lexical_rules( _, (X, _) ) :-
	var(X), !.

print_used_lexical_rules( Id, (A @ B, _) ) :-
	!, print_used_lexical_rules(Id, A),
	print_used_lexical_rules(Id, B).

print_used_lexical_rules( Id, ((A, Ty), Type) ) :-
	!, type_to_pretty_type(Ty, P_Ty),
	type_to_pretty_type(Type, P_Type),
	term_to_atom(P_Ty, A_Ty),
	term_to_atom(P_Type, A_Type),
	ttTerm_to_prettyTerm((A, Ty), AtomTerm), 
	write(Id), write(': '), write(AtomTerm), write(': '),
	write(A_Ty), write(' ----> '), writeln(A_Type),
	print_used_lexical_rules(Id, (A, Ty)). 

print_used_lexical_rules( Id, (abst(_,A), _) ) :-
	!, print_used_lexical_rules(Id, A).

print_used_lexical_rules( _, (TLP, _) ) :-
	TLP =.. [tlp|_].




type_to_pretty_type(A:X, B) :-
	!,
	( var(X) -> B = A;	B = A:X ).	

type_to_pretty_type(A~>B, A1~>B1) :-
	!,
	type_to_pretty_type(A, A1),
	type_to_pretty_type(B, B1).

type_to_pretty_type(A, A) :-
	atom(A).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% extract used tableau rules from history & print


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% extract verbs and nouns from a problem 
%concepts_from_problems( Problems, List) :-

concepts_from_data :-
	findall(PrID, sen_id(_,PrID,_,_,_), PrIDs1),
	remove_adjacent_duplicates(PrIDs1, PrIDs),
	maplist(concepts_from_problem, PrIDs, Sets), 
	%writeln_list(Sets).
	maplist(all_pairs_from_set, Sets, List_of_Pairs), writeln_list(List_of_Pairs). 
	
	
	

% concepts fropm a single problem
concepts_from_problem(ProbID, Set) :-
	findall(CCG, (sen_id(ID, ProbID,_,_,_), ccg(ID,CCG)), CCGs),
	maplist(ccgTree_to_correct_ccgTerm, CCGs, CCGterms), % from CCG terms!
	maplist(concepts_from_ttTerm, CCGterms, List),
	append(List, Concepts),
	list_to_set_using_match(Concepts, Set).

% Extract concepts from a TTterm
concepts_from_ttTerm( (X, _Type), [] ) :-
	var(X), !.

concepts_from_ttTerm( (tlp(_Tk,Lm,POS,_F1,_F2), Type), Set ) :-
	atom_chars(POS, ['N','N'|_]),
    !, nonvar(Lm),
	type_to_prettyType(Type, _Ty),
	% specify what to extracted
	%Set = [(tlp(Tk,Lm,POS,F1,F2), Ty)].
	Set = [Lm].

concepts_from_ttTerm( (tlp(_Tk,_Lm,_POS,_F1,_F2), _Type), [] ) :- !.

concepts_from_ttTerm( (TT1@TT2, _Type), Set ) :-
	!, concepts_from_ttTerm(TT1, List1),
	concepts_from_ttTerm(TT2, List2),
	append(List1, List2, List),
	list_to_set_using_match(List, Set).

concepts_from_ttTerm( (abst(_,TT), _Type), Set ) :-
	!, concepts_from_ttTerm(TT, List),
	list_to_set_using_match(List, Set).

concepts_from_ttTerm( ((TT,Ty), _Type), Set ) :-
	!, concepts_from_ttTerm((TT,Ty), List),
	list_to_set_using_match(List, Set).
	
	


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
pr_lex_rules_from_CorrTerm(CCG_ID) :-
	ccgIDTree_to_ccgIDTerm(CCG_ID, ccg(Id, CCGTerm)),
	ne_ccg(CCGTerm, CCGTerm_1),
	clean_ccgTerm_once(CCGTerm_1, CCGTerm_2),
	CCGTerm_final = CCGTerm_2,
	correct_ccgTerm(CCGTerm_final, Corr_CCGTerm_final),
	print_used_lexical_rules(Id, Corr_CCGTerm_final).

















