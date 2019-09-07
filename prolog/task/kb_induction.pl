%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Induction of lexical relations from an open tableau
% which cause the tableu to close according to the gold answer
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%:- ensure_loaded(['../knowledge/induced_kb'
%				 ]).

:- use_module('../rules/rules', [op(610, xfx, ===>)]).
:- use_module('../printer/reporting', [report/1]).
:- use_module('../lambda/lambda_tt', [op(605, yfx, @)]).
:- use_module('../utils/user_preds', [
	list_to_freqList/2, rm_equi_set_of_facts_/2, shared_members/2, sort_list_length/2,
	sublist_of_list/2, two_lists_to_pair_list/3, prob_input_to_list/2, jobsList_into_N_jobs_rest/3
	]).
:- use_module('../printer/reporting', [report/2]).
:- use_module('../llf/ttterm_to_term', [ttTerm_to_prettyTerm/2]).
:- use_module(library(pairs)).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Given a list of problems with possibly specified answers,
% loop over the problems and induce KB untill it is not possible
induce_knowledge(ToSolve, Answers, UnsolvedProbIDs, Align, Check, KB) :-
	prob_input_to_list(ToSolve, ToSolve1),
	findall( PrId-Ans, (
		member(PrId,ToSolve1), sen_id(_,PrId,'h',Ans,_), memberchk(Ans,Answers)
		), ToSolve_Ans),
	induce_prove_loop(ToSolve_Ans, UnSolved_Ans, Align, Check, [], List_of_KB_cnt),
	two_lists_to_pair_list(UnsolvedProbIDs, _, UnSolved_Ans),
	print_kb_learning_stages(List_of_KB_cnt, KB).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Print learned knowledge according to the stages
print_kb_learning_stages(List_of_KB_cnt, KB) :-
	length(List_of_KB_cnt, Stages),
	format('~`=t All Learned Knowledge (~w stages) ~`=t~100|~n', [Stages]),
	print_learning_stages(1, List_of_KB_cnt),
	append(List_of_KB_cnt, KB_cnt),
	keysort(KB_cnt, KB_cnt_srt),
	two_lists_to_pair_list(_, KB, KB_cnt_srt),
	length(KB_cnt_srt, Len),
	format('~`=t All together (~w rels) ~`=t~100|~n', [Len]),
	maplist(writeln, KB_cnt_srt),
	( debMode(waif(FileName)) -> write_induced_kb_in_file(KB_cnt_srt, FileName); true ).

print_learning_stages(N, [H|Rest]) :-
	!, format('~`-t Stage ~w ~`-t~100|~n', [N]),
	maplist(writeln, H),
	N1 is N + 1,
	print_learning_stages(N1, Rest).

print_learning_stages(_, []).

% write induced knowledge in file that is readable by prolog
write_induced_kb_in_file(KB_cnt_srt, FileName) :-
	open(FileName, write, S, [encoding(utf8), close_on_abort(true)]),
	format(S, '~`%t Induced Knowledge ~`%t~50|~n', []),
	maplist(write_kb_as_term(S, 'ind_rel'), KB_cnt_srt),
	close(S).

write_kb_as_term(S, Func, Term) :-
	format(S, '~w(', Func),
	write_term(S, Term, [quoted(true)]),
	writeln(S, ').').


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% loop over the problems: prove problems and induce kb from proved ones,
% then reuse the kb for proving & inducing new kb from the rest of the unproved problems
induce_prove_loop(ToSolve_Ans, UnSolved_Ans, Align, Check, Init_KB, List_of_KB_cnt) :-
	kb_induction_all(ToSolve_Ans, UnSol_Ans, Align, Check, Init_KB, KB_cnt),
	( ToSolve_Ans == UnSol_Ans ->
		report(['No improvemnet. Stop!']),
		List_of_KB_cnt = [],
		UnSolved_Ans = UnSol_Ans
	; length(ToSolve_Ans, ToLen), length(UnSol_Ans, UnLen),
		format('Improvement from ~w to ~w. Continue~n', [ToLen, UnLen]),
		two_lists_to_pair_list(_, KB, KB_cnt),
	  	append(Init_KB, KB, Init_KB1),
		induce_prove_loop(UnSol_Ans, UnSolved_Ans, Align, Check, Init_KB1, List_of_KB_cnt1),
		List_of_KB_cnt = [KB_cnt|List_of_KB_cnt1]
	), !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Induce knowledge
kb_induction_all(ToSolve_Ans, Unsolved_Ans, Align, Check, KB0, KB_cnt) :-
	( debMode(parallel(Cores)) ->
		jobsList_into_N_jobs_rest(ToSolve_Ans, Cores, JobList),
		concurrent_maplist(kb_induction_some(Align,Check,KB0), JobList, List_of_KBs, List_of_Stats_Ans),
		append(List_of_KBs, KBs),
		append(List_of_Stats_Ans, Stats_Ans)
	; kb_induction_some(Align, Check, KB0, ToSolve_Ans, KBs, Stats_Ans)
	),
	%findall(Stat_Ans-KB1, (
	%	member(PrId_Ans, ToSolve_Ans),
	%    kb_induction_prob(PrId_Ans, Align, Check, KB0, List_KB, Stat_Ans),
	%    ( List_KB = [] -> KB1 = [];  List_KB = [KB1|_] )
	%  ), UnsAns_KBs),
	%two_lists_to_pair_list(Uns_Ans, KBs, UnsAns_KBs),
	findall(U-A, (member(U-A,Stats_Ans), integer(U)), Unsolved_Ans),
    append(KBs, KB_list),
    list_to_freqList(KB_list, KB_cnt),
	format('~`*t Learned knowledge ~`*t~100|~n'),
	maplist(writeln, KB_cnt),
	length(Unsolved_Ans, N),
	format('Unsolved Problems (~w):~n~w~n~`*t~100|~n', [N, Unsolved_Ans]).

% predicate tailored for concurrent_maplist
kb_induction_some(Align, Check, KB0, PrIds_Answers, KBs, Stats_Answers) :-
	maplist(kb_induction_prob(Align,Check,KB0), PrIds_Answers, List_of_list_of_KBs, Stats_Answers),
	findall(KB, (
		member(List_of_KBs, List_of_list_of_KBs),
		(List_of_KBs=[] -> KB=[]; List_of_KBs=[KB|_])
		), KBs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Induce knowledge from a single problem
kb_induction_prob(Align, ConstCheck, KB0, PrId-Ans, Learned_KBs, Stat_Ans) :-
    findall(Sen, (
		sen_id(_,PrId,PH,_,Sent), atomic_list_concat([PH,Sent],': ',Sen)
		), Sentences),
    Patterns = [_, _@_, (_@_)@_, _@(_@_)],
    % Get branches
    get_branches(PrId, Ans, Align, KB0, KB3, TTterms, Branches, Status),
    !,
	( Branches = [] ->
		format('~w (~w): closed [~w]~n', [PrId, Ans, Status]),
		Stat_Ans = 'closed'-Ans
	; discover_knowledge(ConstCheck, TTterms, Branches, KB3, Patterns, Learned_KBs)
	),
	( Branches = [] ->
		format('~w (~w): closed [~w]~n', [PrId, Ans, Status]),
		Stat_Ans = 'closed'-Ans
	; Learned_KBs = [] ->
		format('~w (~w): no KB [~w]~n', [PrId, Ans, Status]),
		Stat_Ans = PrId-Ans,
		maplist(writeln, Sentences)
	; format('~w (~w): !! KB [~w], KB: ~w~n', [PrId, Ans, Status, Learned_KBs]),
		Stat_Ans = 'solved'-Ans,
		maplist(writeln, Sentences),
		report(Learned_KBs)
	),
	format('~`-t~50|~n').

% if get_branches fails the produces demmy output
kb_induction_prob(_Align, _ConstCheck, _KB0, PrId-Ans, [], PrId-Ans).

%
discover_knowledge(ConstCheck, TTterms, Branches, KB3, Patterns, Learned_KBs) :-
    % Get relevant closure rules based on the lexicon extacted from Terms
    extract_lex_NNPs_ttTerms(TTterms, Lexicon, _Names),
    findall(RuleN, clause(r(RuleN,closure,_,_,_,_),_), ListClRules), % automatic retival of closure rules
    list_to_ord_set(ListClRules, ClRules),
    select_relevant_rules(Lexicon, ClRules, RelClRules),
    % Find closing knowledge
    maplist( pattern_filtered_nodes(Patterns), Branches, FilteredBranches ),
	findall(K, ( % a list of sets of facts, that can close Branch
	    member(Br,FilteredBranches), closing_knowledge(RelClRules,Br,KB3,K) % K is a list of lists
	    ), PossKB), % a list of lists of lists
	shared_members(KB_list, PossKB),
	findall(Know, (
		member(Know,KB_list), \+includes_bad_fact(Know,Lexicon,KB3)
		), Good_KB_list),
	sort(Good_KB_list, KB_ord),
	rm_equi_set_of_facts_(KB_ord, KB_test),
	( ConstCheck ->
	  	findall(K, (
			member(K,KB_test), maplist(consistency_check(K),TTterms,Checks),
			\+memberchk('Inconsistent',Checks)
		), KB1)
	; KB1 = KB_test
	),
	findall(X, (
		member(X, KB1), \+((member(Y,KB1), X\=Y, sublist_of_list(Y,X)))
		), KB),
	sort_list_length(KB, Learned_KBs).
	%term_to_atom(KB3, At_KB3),


%	n_group_branches(N, BranchList, GrBranches),
%	Patterns = [ (A,_), (A@B,_) ],
%	abduce_by_closure(Patterns, GrBranches, Facts)


%branches_to_cl_isa_branches(Patterns, Branches, Facts) :-
%	maplist( closing_isa_facts(Patterns), Branches, Facts ).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% strip away type and id info from nodes and
% history and constant info from branches
% also delete LLFs not mattching patterns
/*
thinen_branch( Patterns, br(NodeList,_,_), Thin ) :-
    findall( N, (
    	member(Node, NodeList),
    	thinen_node(Patterns, Node, N)
    	),
      Thin).
*/
% strip away type and id info from nodes
% fails for the LLFs not matching the patterns
/*
thinen_node( Patterns, ndId(nd(M, LLF, Args, TF),_Id), Thin ) :-
	maplist(ttTerm_to_prettyTerm, M, Pr_M),
	maplist(ttTerm_to_prettyTerm, Args, Pr_Args),
	ttTerm_to_prettyTerm(LLF, Pr_LLF),
	prettyTerm_of_patterns( Pr_LLF, Patterns),
	Thin = nd(Pr_M, Pr_LLF, Pr_Args, TF).
*/

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% get branch list for a specific entailment problem and its answer
get_branches(PrId, Ans, Align, KB0, KB3, TTterms, Branches, At_Status) :-
	%prepare rule list, LLFs, and KB
    set_rule_eff_order,
    problem_to_ttTerms('both', PrId, Prem_TTs, Hypo_TTs, Align_Prem_TTs, Align_Hypo_TTs, KB1),
    append(KB0, KB1, KB2),
    sort(KB2, KB3),
    append(Prem_TTs, Hypo_TTs, NoAlign_TTterms),
    append(Align_Prem_TTs, Align_Hypo_TTs, Align_TTterms),
    % consistency checking
%    ( maplist(consistency_check(KB3), NoAlign_TTterms, Checks),
%      memberchk('Inconsistent', Checks)	->
%      	(TTterms, Branches, Status) = (NoAlign_TTterms, [], 'Inconsistent sentence')
    ( % build tableau according to align value
      Ans = 'yes' -> % for entailment
    	generateTableau(KB3, Align_Prem_TTs, Align_Hypo_TTs, Branches_al, _, Status_al),
    	( Branches_al = [] ->
    		(TTterms, Branches, Status) = (Align_TTterms, Branches_al, Status_al) %!!! horrible code fix it
    	; generateTableau(KB3, Prem_TTs, Hypo_TTs, Branches_noal, _, Status_noal),
    	    ( Branches_noal \= [], Align = 'align' ->
    	    	(TTterms, Branches, Status) = (Align_TTterms, Branches_al, Status_al)
    	    ; (TTterms, Branches, Status) = (NoAlign_TTterms, Branches_noal, Status_noal)
    	    )
    	)
      % for contradiction
    ; generateTableau(KB3, Align_TTterms, [], Branches_al, _, Status_al),
      ( Branches_al = [] ->
    	  (TTterms, Branches, Status) = (Align_TTterms, Branches_al, Status_al)
      ; generateTableau(KB3, NoAlign_TTterms, [], Branches_noal, _, Status_noal),
          ( Branches_noal \= [], Align = 'align' ->
    	      (TTterms, Branches, Status) = (Align_TTterms, Branches_al, Status_al)
    	    ; (TTterms, Branches, Status) = (NoAlign_TTterms, Branches_noal, Status_noal)
    	  )
      )
    ),
    term_to_atom(Status, At_Status).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Fact is an ISA relation over ttTerms of Patterns that closes Br(anch)
% ID's are stripped away from the Nodes in branches
closing_knowledge(Rules, BrNodes, KB0, KB) :-
	findall(K, (
		member(R, Rules),
		closing_rule_knowledge(BrNodes, R, KB0, K)
		), K_list),
	sort(K_list, KB).

% KB0 (and KB) is sorted. Now KB is of form  [Fact]
closing_rule_knowledge(br(Nodes,_,_), Rule, KB0, KB) :-
	clause( r(Rule, closure, _, _, _, br(HeadNodes,_) ===> _), _Constraints ),
	findHeadNodes(Nodes, HeadNodes, _IDs),
	append(KB0, _, KB0_X),
	r(Rule, closure, _, _, KB0_X, br(HeadNodes, _) ===> _),
	remove_varTail_from_uList(KB0_X, KB_All),
	sort(KB_All, BK_All_Sorted),
	ord_subtract(BK_All_Sorted, KB0, KB).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
includes_bad_fact(List, Lex, KB) :-
	member(X, List),
	bad_fact(X, Lex, KB),
	!.

% identifies bad/nonsensical facts
bad_fact(ant_wn(A, B), _Lex, KB) :-
	memberchk(isa_wn(A, B), KB);
	memberchk(isa_wn(B, A), KB).

bad_fact(disj(A, B), _Lex, KB) :-
	memberchk(isa_wn(A, B), KB);
	memberchk(isa_wn(B, A), KB).

% disj(yong boy, boy)
bad_fact(disj(A, B), _Lex, KB) :-
	atomic_list_concat(A_Words, ' ', A),
	( memberchk(B, A_Words) %! lazy check
	; A_Words = [_A1, A2],
		memberchk(isa_wn(A2, B), KB)
	). % avoids disj(kid, young boy) when isa_wn(boy, kid) SICK-train-3

% disj(smile, smile nearby)
bad_fact(disj(A, B), _Lex, KB) :-
	atomic_list_concat(B_Words, ' ', B),
	( memberchk(A, B_Words) %! lazy check
	; B_Words = [_B1, B2],
		memberchk(isa_wn(B2, A), KB)
	).

% disj(smile nearby, nearby smile)	but bit risky !!
bad_fact(disj(A, B), _Lex, _KB) :-
	atomic_list_concat([X, Y], ' ', A),
	atomic_list_concat([Y, X], ' ', B).

% isa_wn(full, empty)	for SICK-train-90
bad_fact(isa_wn(A, B), _Lex, KB) :-
	memberchk(ant_wn(A, B), KB).

% disj(two, woman)	but bit risky !!
bad_fact(Fact, Lex, _KB) :-
	Fact =.. [_, A, B],
	findall(0, (
		member((A, PosA), Lex),
	   	member((B, PosB), Lex),
	    comparable_pos_tags(PosA, PosB)
	    ), []).

comparable_pos_tags(A, B) :-
	atom_chars(A, [A1,A2|_]),
	atom_chars(B, [B1,B2|_]),
	( A = B
	; [A1, A2] = [B1, B2]
	; memberchk(A, ['CD', 'DT']),
	  memberchk(B, ['CD', 'DT'])
	; memberchk(A, ['JJ', 'RB']), % lone biker & jumps alone 87
	  memberchk(B, ['JJ', 'RB'])
	), !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ttTerm is of form one of the Patterns, where
% In each pattern variables stand for atoms
% e.g., a@man@run is of form A@B@C but not of A@B
pattern_filtered_nodes([], BrNodes, BrNodes).

pattern_filtered_nodes([P|Atterns], BrNodes, Filtered) :-
	% detecting whether BrNodes are Branch or Nodes
	( BrNodes = br(Nodes, Hist, Sig) ->
	    Filtered = br(FilteredNodes, Hist, Sig)
	  ; BrNodes = Nodes,
	    Filtered = FilteredNodes
	), % Filtering modes based on patterns
	findall(NdId, (
		member(NdId, Nodes),
		ndId_of_patterns(NdId, [P|Atterns])
		), FilteredNodes).

ndId_of_patterns(_, []).

ndId_of_patterns(ndId(Node,_), [P|Atterns]) :-
	Node = nd(_, TT, _Args, _TF),
	member(Pat, [P|Atterns]),
	term_variables(Pat, PatVars),
	ttTerm_to_prettyTerm(TT, Pat),
	maplist(atom, PatVars).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% merge branches (by intersection) into at most N non-empty bunches/groups
% group branches in at most N clusters, where grouping is intersection
group_branches_max(N, Branches, Bunches) :-
	group_branches_max(N, Branches, [], Bunches).

% auxiliary predicate, where 3rd argument serves
% as an intermediate bunches/groups
group_branches_max(_, [], Bunches, Bunches).

group_branches_max(N, [Br|Rest], Bunches1, Bunches2) :-
	( % merges first branch with existing bunch (no new bunch is created)
	  select(Bu, Bunches1, Rest1),
		intersection(Br, Bu, [Non|Empty]), % if branches share nodes
	  	Bunches0 = [ [Non|Empty] | Rest1 ]
	; % create a new bunch
	  length(Bunches1, Len),
		N > Len,
		Bunches0 = [Br|Bunches1]
	),
	group_branches_max(N, Rest, Bunches0, Bunches2).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% split List into at most N non-empty parts
split_list_max_ne(N, List, Partition) :-
	split_list_max_ne(N, List, [], Partition).

% auxiliary predicate, where 3rd argument serves
% as an intermediate partition
split_list_max_ne(_, [], Partition, Partition).

split_list_max_ne(N, [H|Rest], LL1, LL2) :-
	( %add new element to partition without changing #parts
	  select(Part, LL1, LL),
	  	LL0 = [ [H|Part] | LL ]
	; %increase #parts by 1
	  length(LL1, Len),
		N > Len,
		LL0 = [ [H] | LL1 ]
	),
	split_list_max_ne(N, Rest, LL0, LL2).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% split list into 2 non-empty parts
% It returns only uniq partitions: first partition is larger/bigger(term order) than second one
% if L is multiset set [a,b,a] than it produces duplicated partitions
split_list_2ne(L, [H1|P1], [H2|P2]) :-
	split_list_in2(L, [H1|P1], [H2|P2]),
	length(P1, N1),
	length(P2, N2),
	( N1 > N2
	; N1 = N2,
		[H1|P1] @>= [H2|P2] %terms are equla or 1 is after 2 in standard order of terms
		% this leads to the unique {[2], [1]} partition for [1,2]
	).

% Split a list into 2 (possibly empty) parts
split_list_in2([], [], []).

split_list_in2([H | Rest], [H | L1], L2) :-
	split_list_in2(Rest, L1, L2).

split_list_in2([H | Rest], L1, [H | L2]) :-
	split_list_in2(Rest, L1, L2).
