%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Induction of lexical relations from an open tableau
% which cause the tableu to close according to the gold answer
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%abduce_KB_from_prob(PrID, Align, ABD) :-
%	( Align == 'align' ->
%		problem_to_ttTerms(Align, PrID, _, _, PrTTs, HyTTs, KB)
%	  ; problem_to_ttTerms('no_align', PrID, PrTTs, HyTTs, _, _, KB)
%	),





	n_group_branches(N, BranchList, GrBranches),
	Patterns = [ (A,_), (A@B,_) ],
	abduce_by_closure(Patterns, GrBranches, Facts)


branches_to_cl_isa_branches(Patterns, Branches, Facts) :-
	maplist( closing_isa_facts(Patterns), Branches, Facts ).  
	
	
% Fact is an ISA relation over ttTerms of Patterns that closes Br(anch) 
closing_isa_fact(Patterns, Br, Fact) :-
	member(X, Patterns),
	member(Y, Patterns),
	choose(Br, ndId(nd(M, LLF1, Args, true), _ID1), Brest),
	ttTerm_of_pattern(LLF1, X),
	choose(Brest, ndId(nd(M, LLF2, Args, false), _ID2), _),
	ttTerm_of_pattern(LLF2, Y),
	Fact = isa(LLF1, LLF2).

closing_isa_facts(Patterns, Br, [F | Acts]) :- 
	findall(Fact, closing_isa_fact(Patterns, Br, Fact), [F | Acts]).


% ttTerm is of Pattern
ttTerm_of_pattern( (Term,_), Pattern) :-
	ttTerm_to_prettyTerm(Pattern, PrPattern),
	term_variables(PrPattern, Vars),
	Pattern = Term,
	maplist(atom, Vars).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% merge branches (by intersection) in List into at most N non-empty branches
% i.e. group branches in at most N clusters, where grouping is intersection
n_group_branches(N, List, Grouping) :-
	n_group_branches(N, List, [], Grouping).

% step predicate, tracks merging
n_group_branches(_, [], Grouping, Grouping).

n_group_branches(N, [Br | Rest], Grouping1, Grouping2) :-
	( choose(Grouping1, Br1, Rest1),
		intersection(Br, Br1, [Non | Empty]), % if branches share nodes
	  	Grouping0 = [ [Non | Empty] | Rest1 ]
	; length(Grouping1, Len),
		N > Len,
		Grouping0 = [ Br | Grouping1 ]
	),
	n_group_branches(N, Rest, Grouping0, Grouping2).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% split List into at most N non-empty partitions
n_partition_list(N, List, Partition) :-
	n_partition_list(N, List, [], Partition).

n_partition_list(_, [], Partition, Partition).

n_partition_list(N, [H | Rest], LL1, LL2) :-
	( choose(LL1, Part, LL),
	  	LL0 = [ [H | Part] | LL ]
	; length(LL1, Len),
		N > Len,
		LL0 = [ [H] | LL1 ]
	),
	n_partition_list(N, Rest, LL0, LL2).





%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% split list into 2 non-empty parts
% if L is not set [a,b,a] than it produces duplicated partitions
split_list_2ne(L, [H1 | P1], [H2 | P2]) :-
	split_list_in2(L, [H1 | P1], [H2 | P2]),
	length(P1, N1),
	length(P2, N2),
	( N1 > N2
	; N1 = N2,
		term_to_atom([H1 | P1], A1),
		term_to_atom([H2 | P2], A2),
		A1 @>= A2
	).

% general partitioning of lists into 2 parts
split_list_in2([], [], []).

split_list_in2([H | Rest], [H | L1], L2) :-
	split_list_in2(Rest, L1, L2).

split_list_in2([H | Rest], L1, [H | L2]) :-
	split_list_in2(Rest, L1, L2).






