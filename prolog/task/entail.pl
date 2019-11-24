%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- use_module('../prover/tableau_analysis').
:- use_module('../knowledge/wn_preds').
:- use_module('../rules/rule_hierarchy', [set_rule_eff_order/0]).
:- use_module('../utils/user_preds', [
	remove_adjacent_duplicates/2, prob_input_to_list/2, partition_list_into_N_even_lists/3,
	at_most_n_random_members_from_list/3,  print_prob/1, ul_append_ul/2
	]).
:- use_module('../printer/conf_matrix', [draw_extended_matrix/1, draw_matrix/1]).
:- use_module('../printer/reporting', [report/1]).
:- use_module('../latex/latex_ttterm', [latex_probs_llfs/2]).
:- use_module('../llf/recognize_MWE', [clean_ccgTerm_once/2]).
:- use_module('../llf/aligner', [align_ttTerms/4]).
:- use_module('../llf/gen_quant', [once_gen_quant_tt/2, gen_quant_tt/2]).
:- use_module('../llf/ccg_term', [ccgIDTree_to_ccgIDTerm/2]).
:- use_module('../llf/correct_term', [correct_ccgTerm/2]).
:- use_module('../llf/ner', [ne_ccg/2]).
:- use_module('../llf/ttterm_preds', [
	extract_lex_NNPs_ttTerms/3, ttTerms_same_type/2,
	normalize_lexicon/2, token_norm_ttTerm/3
	]).
:- use_module('../knowledge/ind_kb', [add_ind_kb/2]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% entailment with the first GQTT
entail_all :- entail_all('both').

entail_all(Align) :-
	findall( (Problem_Id, Answer),
		sen_id(_, Problem_Id, _, Answer, _),
		ProbIds_Answers),
	remove_adjacent_duplicates(ProbIds_Answers, ProblemIds_Answers),
	set_rule_eff_order, % defines an effciency order of rules
	( debMode('proof_tree') -> true; retractall(debMode('proof_tree'))),
	( debMode(parallel(_)) ->
		%concurrent_maplist(solve_entailment(Align), ProblemIds_Answers, Results)
		parallel_solve_entailment(Align, ProblemIds_Answers, Results)
	; maplist(solve_entailment(Align), ProblemIds_Answers, Results)
	),
	draw_extended_matrix(Results).


%(Id, Ans, Provers_Ans, Closed, Status)

% Consideres only problems with specific answers
entail_all([Ans | Rest]) :- entail_all('both', [Ans | Rest]).

entail_all(Align, List_of_Answers) :-
	findall( (Problem_Id, Answer),
		( sen_id(_, Problem_Id, _, Answer, _), member(Answer, List_of_Answers)  ),
		ProbIds_Answers),
	remove_adjacent_duplicates(ProbIds_Answers, ProblemIds_Answers),
	( debMode('proof_tree') -> true; retractall(debMode('proof_tree'))),
	maplist(solve_entailment(Align), ProblemIds_Answers, Results),
	draw_extended_matrix(Results).


% parallel version of solve_entailment
parallel_solve_entailment(Align, ProblemIds_Answers, Results) :-
	debMode(parallel(Cores)),
	partition_list_into_N_even_lists(ProblemIds_Answers, Cores, JobList),
	length(JobList, JobNumber),
	% report Job partition
	report(['Number of jobs: ', JobNumber]),
	maplist(length, JobList, ListJobLength),
	atomic_list_concat(ListJobLength, ', ', JobMessage),
	report(['Length of jobs: ', JobMessage]),
	% Run concurrent solver for all jobs at the same time and collect all the results in the end
	concurrent_maplist(solve_accu_job(Align), JobList, ResultList),
	partition_list_into_N_even_lists(Results, _, ResultList).

solve_accu_job(Align, ProblemIds_Answers, Results) :-
	maplist(solve_entailment(Align), ProblemIds_Answers, Results).



entail_some(List_Int) :-
	entail_some('both', List_Int).

entail_some(Align, List_Int) :-
	prob_input_to_list(List_Int, L1),
	( debMode('singPrem') ->
		findall(X, (member(X,L1), \+findall(_, sen_id(_,X,'p',_,_),[_,_|_])), L2 )
	; L2 = L1
	),
	( debMode('fracFilter') ->
		findall(X, (member(X,L2), \+member(X, [12,16,61,62,77,78,213,276,305,308,309,310])), List )
      ; List = L2
	),
	set_rule_eff_order, % defines an effciency order of rules
	findall( (Problem_Id, Answer),  (member(Problem_Id, List), sen_id(_, Problem_Id, _, Answer, _)),  ProbIds_Answers ),
	remove_adjacent_duplicates(ProbIds_Answers, ProblemIds_Answers),
	( debMode('proof_tree') -> true; retractall(debMode('proof_tree'))),
	( debMode(parallel(_)) ->
		%concurrent_maplist(solve_entailment(Align), ProblemIds_Answers, Results)
		parallel_solve_entailment(Align, ProblemIds_Answers, Results)
	; maplist(solve_entailment(Align), ProblemIds_Answers, Results)
	),
	%maplist(solve_entailment(Align), ProblemIds_Answers, Results),
	draw_extended_matrix(Results).


% bad fracas 12,16,61,62,77,78,213,276,305,308,309,310

% entailment with all GQTTs
% list_entail_all :-
% 	findall( (Problem_Id, Answer),
% 		sen_id(_, Problem_Id, _, Answer, _),
% 		ProbIds_Answers),
% 	remove_adjacent_duplicates(ProbIds_Answers, ProblemIds_Answers),
% 	( debMode('proof_tree') -> true; retractall(debMode('proof_tree'))),
% 	maplist(list_solve_entailment, ProblemIds_Answers, Results),
% 	%draw_matrix(Results).
% 	draw_extended_matrix(Results).


% list_entail_some(List) :-
% 	findall( (Problem_Id, Answer),
% 		( member(Problem_Id, List), sen_id(_, Problem_Id, _, Answer, _) ),
% 		ProbIds_Answers),
% 	remove_adjacent_duplicates(ProbIds_Answers, ProblemIds_Answers),
% 	( debMode('proof_tree') -> true; retractall(debMode('proof_tree'))),
% 	maplist(list_solve_entailment, ProblemIds_Answers, Results),
% 	draw_matrix(Results).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Creates result pairs
% list_solve_entailment( (Id, Answer), (Id, Ans, Closed, Status) ) :-
% 	(Answer = 'undef' ->
% 		Ans = 'unknown'
% 	  ; Ans = Answer
% 	),
% 	list_entail(Id, Ans, Closed, Status),
% 	format('~t~w:~4+~t~w,~9+~t~w,~8+ ~w~t~12+~n', [Id, Ans, Closed, Status]).
/*	list_entail(Id) ->
		( Answer == yes ->  % can deal with answers "yes" and rest
			write(Id), write('-yes,'), writeln(' pass'), Result = (yes, true);
		  	write(Id), write('-no, '), writeln(' fail'), Result = (no, true) );
		( Answer == yes ->
			write(Id), write('-yes,'), writeln(' fail'), Result = (yes, false);
			write(Id), write('-no, '), writeln(' pass'), Result = (no, false) ).
*/

solve_entailment(Align, (Id, Answer), (Id, Ans, Provers_Ans, Closed, Status) ) :-
	( Answer = 'undef' ->
		Ans = 'unknown'
	  ; Ans = Answer
	),
	%( debMode('2class') ->
	%	entail_2(Id, Ans, Provers_Ans, XP, Closed, Status);
	( debMode('shallow') ->
		shallow_reasoning(Id, Provers_Ans, XP_, Closed, Status)%,  Closed = 'closed'
	; entail(Align, Id, Ans, Provers_Ans, XP_, Closed, Status)
	),
	term_to_atom(Status, AtomStatus),
	( debMode('prprb') ->  findall(Sen, sen_id(_,Id,_,_,Sen), Sentences), maplist(writeln, Sentences); true ),
	uList2List(XP_, XP),
	format('~t~w:~5+~t [~w],~11+~t~w,~9+~t~w,~9+ ~w~t~12+ XP: ~w~n', [Id, Ans, Provers_Ans, Closed, AtomStatus, XP]).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Returns List of TTterms corresponding to
% a list of premises and hypothesis
problem_id_TTterms(ProbId, Prem_TTterms, Hypo_TTterms) :-
	findall(TTterm,
		( sen_id(Id, ProbId, 'p', _, _),	% premises
		  ( ccg(Id, CCGTree) ->
				ccgTree_to_TTterm(CCGTree, TTterm);
				atomic_list_concat(['Error: prob', ProbId, ', sent', Id, ' cannot be parsed'], Message),
					writeln(Message), fail ) ),
		Prem_TTterms),
	findall(TTterm,
		( sen_id(Id, ProbId, 'h', _, _),	% hypothesis
		  ( ccg(Id, CCGTree) ->
				ccgTree_to_TTterm(CCGTree, TTterm);
				atomic_list_concat(['Error: prob', ProbId, ', sent', Id, ' cannot be parsed'], Message),
					writeln(Message), fail ) ),
		Hypo_TTterms).


% Returns List of list of TTterms,
% where each premise and hypotheses
% are mapped to list of TTterms
% due to several representation caused by genGuant
problem_id_list_TTterms(ProbId, List_Prem_TTterms, List_Hypo_TTterms) :-
	findall(TTterms,
		( sen_id(Id, ProbId, 'p', _, _), % premises
		  ( ccg(Id, CCGTree) ->
				ccgTree_to_TTterms(CCGTree, TTterms)
			;	report(['Error: prob', ProbId, ', sent', Id, ' cannot be parsed']),
				fail
		  )
		),
		List_Prem_TTterms),
	findall(TTterms,
		( sen_id(Id, ProbId, 'h', _, _),	% hypothesis
		  ( ccg(Id, CCGTree) ->
				ccgTree_to_TTterms(CCGTree, TTterms)
			;	report(['Error: prob', ProbId, ', sent', Id, ' cannot be parsed']),
				fail
		  )
		),
		List_Hypo_TTterms).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% checks on entailment a problem with its Id
% uses a single reading
check_problem(KB_XP, Prem_TTterms, Hypo_TTterms, 'yes', Provers_Ans, Closed, Status, Tree) :-
	!,
	( generateTableau(KB_XP, Prem_TTterms, Hypo_TTterms, BrList, Tree, Status) ->
		%( integer(Steps) ->
		%	Status = ('Ter', Steps)
		%;	Status = 'Limited'),
		( BrList = [] ->
			Closed = 'closed', Provers_Ans = 'yes'
		;	Closed = 'open',   Provers_Ans = 'unknown'
		)
	; 	Closed = 'NA',
		Provers_Ans = 'unknown',
		Status = 'Defected'
	).

check_problem(KB_XP, Prem_TTterms, Hypo_TTterms, 'no_unk', Provers_Ans, Closed, Status, Tree) :- %Wrong
	!,
	check_problem(KB_XP, Prem_TTterms, Hypo_TTterms, 'yes', Provers_Ans, Closed, Status, Tree).



check_problem(KB_XP, Prem_TTterms, Hypo_TTterms, 'no', Provers_Ans, Closed, Status, Tree) :-
	!,
	append(Prem_TTterms, Hypo_TTterms, TTterms),
	( %fail,
	  generateTableau(KB_XP, TTterms, [], BrList, Tree, Status) ->
		%( integer(Steps) ->
		%	Status = 'Terminated'
		%;	Status = 'Limited'),
		( BrList = [] ->
			Closed = 'closed', Provers_Ans = 'no'
		;	Closed = 'open',   Provers_Ans = 'unknown'
		)
	; 	Closed = 'NA',
		Provers_Ans = 'unknown',
		Status = 'Defected'
	).

check_problem(KB-XP, Prem_TTterms, Hypo_TTterms, 'unknown', Provers_Ans, Closed, Status, _) :-
	!,
	check_problem(KB-XP_yes, Prem_TTterms, Hypo_TTterms, 'yes', Provers_Ans_yes, Closed_yes, Status_yes, _Tree1),
	check_problem(KB-XP_no, Prem_TTterms, Hypo_TTterms, 'no', Provers_Ans_no, Closed_no, Status_no, _Tree2),
	( Closed_yes == 'closed' ->
		(Provers_Ans, Closed, Status, XP) = (Provers_Ans_yes, Closed_yes, Status_yes, XP_yes)
	; Closed_no == 'closed' ->
		(Provers_Ans, Closed, Status, XP) = (Provers_Ans_no, Closed_no, Status_no, XP_no)
	; ( Closed_yes == 'NA'; Closed_no == 'NA' ) ->
		(Provers_Ans, Closed, Status, XP) = ('unknown', 'NA', 'Defected', [])
	; ( Status_yes = ('Lim',_); Status_no = ('Lim',_) ) ->
		Status_yes = (_,Steps1),
		Status_no = (_,Steps2),
		Steps is Steps1 + Steps2,
		(Provers_Ans, Closed, Status, XP) = ('unknown', 'open', ('Lim',Steps), [])
	; Status_yes = (_, Steps1),
	  Status_no = (_, Steps2),
	  Steps is Steps1 + Steps2,
	  (Provers_Ans, Closed, Status, XP) = ('unknown', 'open', ('Ter',Steps), [])
	).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% solves a problem vs check
solve_problem(PrId, KB-XP, Prem_TTterms, Hypo_TTterms, Prover_Ans, Closed, Status) :-
	check_problem(KB-XP_yes, Prem_TTterms, Hypo_TTterms, 'yes', _, Closed_yes, Status_yes, Tree_yes),
	check_problem(KB-XP_no, Prem_TTterms, Hypo_TTterms, 'no', _,  Closed_no, Status_no, Tree_no),
	( (Closed_yes, Closed_no) == ('closed', 'closed') ->
		report(['Warning: CONTRADICTION and ENTAILMENT at the same time: so NEUTRAL']),
		copy_term(XP_yes, XP),
		ul_append_ul(XP, XP_no),
		(Prover_Ans, Closed, Status) = ('unknown', 'open', 'Terminated')%,  %!!!
		%report_theUsedrules_in_tree(Tree_yes),
		%report_theUsedrules_in_tree(Tree_no)
	; (Closed_yes, Closed_no) == ('closed', 'open') ->
		(Prover_Ans, Closed, Status, XP)  = ('yes', Closed_yes, Status_yes, XP_yes),
		( theUsedrules_in_tree(Tree_yes, [H|T]) -> report([PrId, ': ', [H|T]]); true )
	; (Closed_yes, Closed_no) == ('open', 'closed') ->
		(Prover_Ans, Closed, Status, XP)  = ('no', Closed_no, Status_no, XP_no),
		( theUsedrules_in_tree(Tree_no, [H|T]) -> report([PrId, ': ', [H|T]]); true )
	; (Closed_yes, Closed_no) == ('open', 'open') ->
		Status_yes = (_,Steps1),
		Status_no  = (_,Steps2),
		Steps is Steps1 + Steps2,
		( (Status_yes = ('Lim',_); Status_no = ('Lim',_)) ->
			Status = ('Lim',Steps)
	  	  ; Status = ('Ter',Steps)
		),
		(Prover_Ans, Closed, XP)  = ('unknown', 'open', _)%,
		%report_theUsedrules_in_tree(Tree_yes),
		%report_theUsedrules_in_tree(Tree_no)
   	; (Closed_yes == 'NA'; Closed_no == 'NA') ->
		(Prover_Ans, Closed, Status, XP)  = ('unknown', 'NA', 'Defected', _)
	; report(['Error: this should not had happened'])
	).
/*
% checks problems - knows the answer beforehand
entail(Problem_Id, Answer, Provers_Answer, Closed, FinalStatus) :-
	findall(_X, sen_id(_, Problem_Id, _, _, _), Prem_Hyp), % finds the length of the problem
	%problem_id_TTterms(Problem_Id, Prem_TTs, Hypo_TTs), Align_Prem_TTs = Prem_TTs, Align_Hypo_TTs = Hypo_TTs,
	problem_to_ttTerms('align', Problem_Id, Prem_TTs, Hypo_TTs, Align_Prem_TTs, Align_Hypo_TTs),
	check_problem(Prem_TTs, Hypo_TTs, Answer, NoA_Prov_Ans, NoA_Closed, NoA_Status),
	check_problem(Align_Prem_TTs, Align_Hypo_TTs, Answer, Align_Prov_Ans, Align_Closed, Align_Status),
	( Align_Closed \== 'closed', NoA_Closed \== 'closed', \+append(Prem_TTs, Hypo_TTs, Prem_Hyp) -> % if an item in the problem is defected
		(Provers_Answer, Closed, FinalStatus) = ('unknown', 'NA', 'Defected')
	; Align_Closed == 'closed' ->
		(Provers_Answer, Closed, FinalStatus) =  (Align_Prov_Ans, Align_Closed, Align_Status)
    ; (Provers_Answer, Closed, FinalStatus)   =  (NoA_Prov_Ans, NoA_Closed, NoA_Status)
	),	!.
*/


% checks an LLF on consistency, faisl if it is not consistent
consistency_check(KB_XP, LLF, Answer) :-
	check_problem(KB_XP, [LLF], [], 'yes', _PrAns, Closed, _Status, _Tree),
	%ignore(greason(KB, [LLF], [], 1)), % testing sentences separetly
	memberchk((Closed, Answer), [('open','Consistent'), ('closed','Inconsistent'), ('NA', 'Defected')]).




%/*
% solves problems - doesnt knows the answer beforehand
entail(Align, PrId, _Answer, Provers_Answer, XP, Closed, FinalStatus) :-
	% writeln(PrId),
	findall(_X, sen_id(_, PrId, _, _, _), Prem_Hyp), % finds the length of the problem
	%problem_id_TTterms(PPrId, Prem_TTs, Hypo_TTs), Align_Prem_TTs = Prem_TTs, Align_Hypo_TTs = Hypo_TTs,
	problem_to_ttTerms(Align, PrId, Prem_TTs, Hypo_TTs, Align_Prem_TTs, Align_Hypo_TTs, KB),
	append(Prem_TTs, Hypo_TTs, LLFs),
	( ttTerms_same_type(LLFs, _Type) ->
	  ( debMode('constchk') -> maplist(consistency_check(KB-[]), LLFs, Checks); Checks = [] ), % no explanation from consistency checking
	  ( memberchk('Inconsistent', Checks) ->
		  atomic_list_concat(Checks, ', ', Text), report(['Warning: CONTRADICTION found in an LLF:\n', Text]),
		  (Provers_Answer, Closed, FinalStatus, XP) = ('unknown', 'NA', 'Defected', _)
	  ; Align = 'align' ->
	  	  solve_problem(PrId, KB-XP, Align_Prem_TTs, Align_Hypo_TTs, Provers_Answer, Closed, FinalStatus)
	  ; Align = 'no_align' ->
		  solve_problem(PrId, KB-XP, Prem_TTs, Hypo_TTs, Provers_Answer, Closed, FinalStatus)
	  ; solve_problem(PrId, KB-XPna, Prem_TTs, Hypo_TTs, NoA_Prov_Ans, NoA_Closed, NoA_Status),
	    solve_problem(PrId, KB-XPal, Align_Prem_TTs, Align_Hypo_TTs, Align_Prov_Ans, Align_Closed, Align_Status),
	    ( Align_Closed \== 'closed', NoA_Closed \== 'closed', \+append(Prem_TTs, Hypo_TTs, Prem_Hyp) -> % if an item in the problem is defected
		    (Provers_Answer, XP, Closed, FinalStatus) = ('unknown', _, 'NA', 'Defected')
	    ; Align_Closed == 'closed' ->
		    (Provers_Answer, XP, Closed, FinalStatus) =  (Align_Prov_Ans, XPal, Align_Closed, Align_Status)
        ; (Provers_Answer, XP, Closed, FinalStatus)   =  (NoA_Prov_Ans, XPna, NoA_Closed, NoA_Status)
	    )
      ), !
    ; report(['Inconsistency in node types - entail']),
	  (Provers_Answer, Closed, FinalStatus) = ('unknown', 'NA', 'Defected')
	).
%*/

% entailment for binary classification
% not maintained yet
% entail_2(Problem_Id, _Answer, Provers_Answer, Closed, FinalStatus) :-
% 	findall(_X, sen_id(_, Problem_Id, _, _, _), Prem_Hyp), % finds the length of the problem
% 	%problem_id_TTterms(Problem_Id, Prem_TTs, Hypo_TTs), Align_Prem_TTs = Prem_TTs, Align_Hypo_TTs = Hypo_TTs,
% 	problem_to_ttTerms('align', Problem_Id, Prem_TTs, Hypo_TTs, Align_Prem_TTs, Align_Hypo_TTs, KB),
% 	% check on yes entailment both non-aligned and aligned TTs
% 	check_problem(KB_XP, Prem_TTs, Hypo_TTs, 'yes', _, NoA_Closed, NoA_Status, _),
% 	check_problem(KB_XP, Align_Prem_TTs, Align_Hypo_TTs, 'yes', _, Al_Closed, Al_Status, _),
% 	% compute final answer
% 	( Al_Closed \== 'closed', NoA_Closed \== 'closed', \+append(Prem_TTs, Hypo_TTs, Prem_Hyp) -> % if an item in the problem is defected
% 		(Provers_Answer, Closed, FinalStatus) = ('no_unk', 'NA', 'Defected')
% 	; Al_Closed == 'closed' ->
% 		(Provers_Answer, Closed, FinalStatus) =  ('yes', Al_Closed, Al_Status)
%     ; NoA_Closed == 'closed' ->
% 		(Provers_Answer, Closed, FinalStatus)   =  ('yes', NoA_Closed, NoA_Status)
% 	; (Provers_Answer, Closed, FinalStatus)   =  ('no_unk', NoA_Closed, NoA_Status)
% 	),	!.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% checks on entailment a problem with its Id
% uses several readings
% Not maintained yet
% list_entail(Problem_Id, Answer, Closed, FinalStatus) :-
% 	findall(_X, sen_id(_, Problem_Id, _, _, _), Prem_Hyp), % finds the length of the problem
% 	%problem_id_list_TTterms(Problem_Id, List_Prem_TTterms, List_Hypo_TTterms),
% 	problem_to_list_ttTerms('align', Problem_Id, List_Prem_TTterms, List_Hypo_TTterms, List_Align_Prem_TTterms, List_Align_Hypo_TTterms, KB),
% 	% once(list_reason(List_of_Lists)).
% 	%( append(List_Prem_TTterms, List_Hypo_TTterms, Prem_Hyp) ->
% 	( maplist(member, Prem_TTterms, List_Prem_TTterms),
%       maplist(member, Hypo_TTterms, List_Hypo_TTterms),
% 	  %once(append(TextList, [Hypo], TTterms)),
% 	  check_problem(KB_XP, Prem_TTterms, Hypo_TTterms, Answer, _, 'closed', NoA_Status, _) ->
% 		  NoA_Closed = 'closed'
% 		  %Status = Status1
% 	    ; NoA_Closed = 'open',
% 		  once(  (maplist(member, Prem_TTterms, List_Prem_TTterms),
% 	  	          maplist(member, Hypo_TTterms, List_Hypo_TTterms))  ),
% 		  check_problem(KB_XP, Prem_TTterms, Hypo_TTterms, Answer, _, _Open1, NoA_Status, _)
% 	),
% 	( maplist(member, Align_Prem_TTterms, List_Align_Prem_TTterms),
%       maplist(member, Align_Hypo_TTterms, List_Align_Hypo_TTterms),
% 	  %once(append(TextList, [Hypo], TTterms)),
% 	  check_problem(KB_XP, Align_Prem_TTterms, Align_Hypo_TTterms, Answer, _, 'closed', Align_Status, _) ->
% 		  Align_Closed = 'closed'
% 		  %Status = Status1
% 	    ; Align_Closed = 'open',
% 		  once(  (maplist(member, Align_Prem_TTterms, List_Align_Prem_TTterms),
% 	  	          maplist(member, Align_Hypo_TTterms, List_Align_Hypo_TTterms))  ),
% 		  check_problem(KB_XP, Align_Prem_TTterms, Align_Hypo_TTterms, Answer, _, _Open2, Align_Status, _)
% 	),
% 	( Align_Closed \= 'closed',
% 	  NoA_Closed \= 'closed',
% 	  \+append(List_Prem_TTterms, List_Hypo_TTterms, Prem_Hyp) -> % if an item in the problem is defected
% 		FinalStatus = 'Defected'
% 	  ; ( Align_Closed = 'closed' ->
% 		    FinalStatus = Align_Status, Closed = Align_Closed
%           ; FinalStatus = NoA_Status,   Closed = NoA_Closed
% 		)
% 	),
% 	!.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% checks on GUI entailment a problem with its Id
% uses a single reading
gentail(Problem_Id) :-
	gentail('no_align', Problem_Id).

gentail(Align, Problem_Id) :-
	set_rule_eff_order, % defines an effciency order of rules
	once(sen_id(_, Problem_Id, _, Answer, _)),
	%problem_id_TTterms(Problem_Id, Prem_TTterms, Hypo_TTterms),
	( Align == 'align' ->
		problem_to_ttTerms(Align, Problem_Id, _, _, Prem_TTterms, Hypo_TTterms, KB)
	  ; problem_to_ttTerms('no_align', Problem_Id, Prem_TTterms, Hypo_TTterms, _, _, KB)
	),
	%findall(ccg(Id, CCGTree),
	%		( sen_id(Id, Problem_Id, _, _, _),
	%		  ccg(Id, CCGTree) ),
	%		CCG_IDs
	%),
	%ccgs_to_llfs_latex(CCG_IDs),
	append(Prem_TTterms, Hypo_TTterms, TTterms),
	atomic_list_concat(['LLF_Prob-', Problem_Id], FileName),
	( debMode('tex') -> latex_probs_llfs([Problem_Id], FileName); true ),
	( Prem_TTterms = [], Hypo_TTterms = [] ->
		writeln('Problem with this id plausibly does not exist!')
	; Prem_TTterms = [] ->
		writeln('No premises found for this problem!')
	; Hypo_TTterms = [] ->
		writeln('No hypothesis found for this problem!')
	;	% Reason! problem is ok
	  Answer = 'no' ->
		greason(KB-XP_, TTterms, [], [Problem_Id, 'no', Align])
	; Answer = 'yes' ->
		greason(KB-XP_, Prem_TTterms, Hypo_TTterms, [Problem_Id, 'yes', Align])
	; greason(KB-XP_, Prem_TTterms, Hypo_TTterms, [Problem_Id, 'yes', Align]) ->
		true
	; greason(KB-XP_, TTterms, [], [Problem_Id, 'no', Align])
	),
	uList2List(XP_, XP),
	format('XP: ~w~n', [XP]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% doesnt take into account answer of the problem
gentail_no_answer(Problem_Id) :-
	gentail_no_answer('no_align', Problem_Id).

gentail_no_answer(Align, Problem_Id) :-
	set_rule_eff_order, % defines an effciency order of rules
	once(sen_id(_, Problem_Id, _, Answer, _)),
	%problem_id_TTterms(Problem_Id, Prem_TTterms, Hypo_TTterms),
	( Align == 'align' ->
		problem_to_ttTerms(Align, Problem_Id, _, _, Prem_TTterms, Hypo_TTterms, KB)
	  ; problem_to_ttTerms('no_align', Problem_Id, Prem_TTterms, Hypo_TTterms, _, _, KB)
	),
	%findall(ccg(Id, CCGTree),
	%		( sen_id(Id, Problem_Id, _, _, _),
	%		  ccg(Id, CCGTree) ),
	%		CCG_IDs
	%),
	%ccgs_to_llfs_latex(CCG_IDs),
	atomic_list_concat(['LLF_Prob-', Problem_Id], FileName),
	( debMode('tex') -> latex_probs_llfs([Problem_Id], FileName); true ),
	append(Prem_TTterms, Hypo_TTterms, TTterms),
	( Prem_TTterms = [], Hypo_TTterms = [] ->
		writeln('Problem with this id plausibly does not exist!')
	; Prem_TTterms = [] ->
		writeln('No premises found for this problem!')
	; Hypo_TTterms = [] ->
		writeln('No hypothesis found for this problem!')
	;	% Reason! problem is ok
	  Answer = 'no' ->
		%append(Prem_TTterms, Hypo_TTterms, TTterms),
		ignore(greason(KB-_, Prem_TTterms, Hypo_TTterms, [Problem_Id, 'yes', Align])),
		greason(KB-XP_, TTterms, [], [Problem_Id, 'no', Align])
	; Answer = 'yes' ->
		ignore(greason(KB-_, TTterms, [], [Problem_Id, 'no', Align])),
		greason(KB-XP_, Prem_TTterms, Hypo_TTterms, [Problem_Id, 'yes', Align])
	; greason(KB-XP_, Prem_TTterms, Hypo_TTterms, [Problem_Id, 'yes', Align]) ->
		true
	; %append(Prem_TTterms, Hypo_TTterms, TTterms),
	  greason(KB-XP_, TTterms, [], [Problem_Id, 'no', Align])
	),
	uList2List(XP_, XP),
	format('XP: ~w~n', [XP]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Take a problem id and a sign and assign this sign to all sentences in the problem
% used for analysis of single sentences
ganalysis(Sign, Problem_Id) :-
	problem_to_ttTerms('no_align', Problem_Id, Prem_TTterms, Hypo_TTterms, _, _, KB),
	%findall(ccg(Id, CCGTree),
	%		( sen_id(Id, Problem_Id, _, _, _),  ccg(Id, CCGTree) ),
	%		CCG_IDs
	%),
	%ccgs_to_llfs_latex(CCG_IDs),
	atomic_list_concat(['LLF_Prob-', Problem_Id], FileName),
	( debMode('tex') -> latex_probs_llfs([Problem_Id], FileName); true ),
	append(Prem_TTterms, Hypo_TTterms, TTterms),
	( Sign = 'true' ->
		greason(KB-XP_, TTterms, [], Problem_Id)
	; Sign = 'false' ->
		greason(KB-XP_, [], TTterms, Problem_Id)
	),
	uList2List(XP_, XP),
	format('XP: ~w~n', [XP]).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% checks on GUI entailment a problem with its Id
% uses several readings
% list_gentail(Problem_Id) :-
% 	list_gentail('no_align', Problem_Id).
%
% list_gentail(Align, Problem_Id) :-
% 	once(sen_id(_, Problem_Id, _, Answer, _)),
% 	%problem_id_list_TTterms(Problem_Id, List_Prem_TTterms, List_Hypo_TTterms),
% 	( Align == 'align' ->
% 		problem_to_list_ttTerms(Align, Problem_Id, _, _, List_Prem_TTterms, List_Hypo_TTterms, KB)
% 	  ; problem_to_list_ttTerms('no_align', Problem_Id, List_Prem_TTterms, List_Hypo_TTterms, _, _, KB)
% 	),
% 	%once(list_reason(List_of_Lists)).
% 	maplist(member, Prem_TTterms, List_Prem_TTterms),
% 	maplist(member, Hypo_TTterms, List_Hypo_TTterms),
% 	%once(append(TextList, [Hypo], TTterms)),
% 	( Answer = 'no' ->
% 		append(Prem_TTterms, Hypo_TTterms, New_Prem_TTterms),
% 		New_Hypo_TTterms = []
% 	  ; New_Prem_TTterms = Prem_TTterms,
% 		New_Hypo_TTterms = Hypo_TTterms
% 	),
% 	greason(KB-_, New_Prem_TTterms, New_Hypo_TTterms, Problem_Id).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
/*list_reason(List_of_Lists) :-
	maplist(member, TTterms, List_of_Lists),
	once(append(TextList, [Hypo], TTterms)),
	reason(TextList, [Hypo]).

list_greason(List_of_Lists) :-
	maplist(member, TTterms, List_of_Lists),
	once(append(TextList, [Hypo], TTterms)),
	greason(TextList, [Hypo]).*/




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Produces a single TTterm from a CCGTerm
ccgTree_to_TTterm(CCGTree, TTterm) :-
	ccgIDTree_to_ccgIDTerm(ccg(_,CCGTree), ccg(_,CCGTerm1)),
	ne_ccg(CCGTerm1, CCGTerm2),
	clean_ccgTerm_once(CCGTerm2, CCGTerm3),
	correct_ccgTerm(CCGTerm3, CCGTerm4),
	%gen_quant_tt(CCGTerm4, TTterms).
	once_gen_quant_tt(CCGTerm4, TTterm).

% Produces a list of all possible TTterms from a CCGTerm
ccgTree_to_TTterms(CCGTree, TTterms) :-
	ccgIDTree_to_ccgIDTerm(ccg(_,CCGTree), ccg(_,CCGTerm1)),
	ne_ccg(CCGTerm1, CCGTerm2),
	clean_ccgTerm_once(CCGTerm2, CCGTerm3),
	correct_ccgTerm(CCGTerm3, CCGTerm4),
	gen_quant_tt(CCGTerm4, TTterms).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
problem_to_ttTerms(Align, Prob_Id, Prems, Hypos, Align_Prems, Align_Hypos, KB) :-
	findall(Sen_Id, sen_id(Sen_Id, Prob_Id, 'p', _, _), Prem_Sen_Ids),
	findall(Sen_Id, sen_id(Sen_Id, Prob_Id, 'h', _, _), Hypo_Sen_Ids),
	findall(CCGTree,	( member(Id, Prem_Sen_Ids), ccg(Id, CCGTree) ),		PremCCGTrees),
	findall(CCGTree, 	( member(Id, Hypo_Sen_Ids), ccg(Id, CCGTree) ),		HypoCCGTrees),
	maplist(ccgTree_to_correct_ccgTerm, PremCCGTrees, PremCCGTerms1),
	maplist(ccgTree_to_correct_ccgTerm, HypoCCGTrees, HypoCCGTerms1),
	% extracting WN_relations for aligning
	append(PremCCGTerms1, HypoCCGTerms1, AllCCGTerms),

	extract_lex_NNPs_ttTerms(AllCCGTerms, Lexicon1, _Names),
	normalize_lexicon(Lexicon1, Lexicon),
	( Lexicon1 \= Lexicon -> report(['Difference in Lemma Lexicons after normalization']); true ),
	maplist( token_norm_ttTerm(Lexicon), PremCCGTerms1, PremCCGTerms ),
	maplist( token_norm_ttTerm(Lexicon), HypoCCGTerms1, HypoCCGTerms ),

	%ground_ccgterms_to_lexicon(),
	( debMode('prlex') -> report([Lexicon]); true),
	%( debMode('subWN') -> subWN_from_wn(Lexicon); kb_from_wn(Lexicon, KB) ),
	( debMode('no_wn') -> KB0 = []; kb_from_wn(Lexicon, KB0) ), % extract relevant semantic relations from WN
	( debMode('ind_kb') -> add_ind_kb(KB0,KB); KB = KB0 ),
	( debMode('pr_kb') -> report(['KB: ', KB]); true ),
	( debMode('no_gq_llfs') ->
		(Prems, Hypos) = (PremCCGTerms, HypoCCGTerms)
	; findall(Y, 	(member(X, PremCCGTerms), once_gen_quant_tt(X, Y)), 	Prems),
	  findall(Y, 	(member(X, HypoCCGTerms), once_gen_quant_tt(X, Y)), 	Hypos)
	),
	% if align flag is on
	( (Align == 'align'; Align == 'both')  ->
		append(PremCCGTerms, HypoCCGTerms, CCGTerms),
		align_ttTerms(CCGTerms, Align_CCGTerms, _SubTerms, KB-[]),
		length(HypoCCGTerms, N),
		append(Align_PremCCGTerms, Align_HypoCCGTerms, Align_CCGTerms),
		length(Align_HypoCCGTerms, N),
		( debMode('no_gq_llfs') ->
			(Align_Prems, Align_Hypos) = (Align_PremCCGTerms, Align_HypoCCGTerms)
	  	  ; findall(Y, 	(member(X, Align_PremCCGTerms), once_gen_quant_tt(X, Y)), 	Align_Prems),
			findall(Y, 	(member(X, Align_HypoCCGTerms), once_gen_quant_tt(X, Y)), 	Align_Hypos)
		)
	  ; Align_Prems = Prems, % if 'no_align' then rturn empty lists
		Align_Hypos = Hypos  % or if 'no_align' then rturn no_aligned ones, easier to swith to align and nonalign
	), !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% for list ttTerms
%
%problem_to_list_ttTerms(Align, Prob_Id, List_Prems, List_Hypos, List_Align_Prems, List_Align_Hypos) :-
problem_to_list_ttTerms(Align, Prob_Id, List_Prems_R, List_Hypos_R, List_Align_Prems_R, List_Align_Hypos_R, []) :- % fix KB\=[]
	findall(Sen_Id, sen_id(Sen_Id, Prob_Id, 'p', _, _), Prem_Sen_Ids),
	findall(Sen_Id, sen_id(Sen_Id, Prob_Id, 'h', _, _), Hypo_Sen_Ids),
	findall(CCGTree,	( member(Id, Prem_Sen_Ids), ccg(Id, CCGTree) ),		PremCCGTrees),
	findall(CCGTree, 	( member(Id, Hypo_Sen_Ids), ccg(Id, CCGTree) ),		HypoCCGTrees),
	maplist(ccgTree_to_correct_ccgTerm, PremCCGTrees, PremCCGTerms),
	maplist(ccgTree_to_correct_ccgTerm, HypoCCGTrees, HypoCCGTerms),
	findall(List_TT, 	(member(X, PremCCGTerms), gen_quant_tt(X, List_TT)), 	List_Prems),
	findall(List_TT, 	(member(X, HypoCCGTerms), gen_quant_tt(X, List_TT)), 	List_Hypos),
	% chosing random readings, not all
	at_most_n_random_members_from_list(List_Prems, 5, List_Prems_R),
	at_most_n_random_members_from_list(List_Hypos, 5, List_Hypos_R),
	% if align flag is on
	( Align == 'align' ->
		append(PremCCGTerms, HypoCCGTerms, CCGTerms),
		align_ttTerms(CCGTerms, Align_CCGTerms, _, _KB_XP), % FIXME
		length(HypoCCGTerms, N),
		append(Align_PremCCGTerms, Align_HypoCCGTerms, Align_CCGTerms),
		length(Align_HypoCCGTerms, N),
		findall(List_TT, 	(member(X, Align_PremCCGTerms), gen_quant_tt(X, List_TT)), 	List_Align_Prems),
		findall(List_TT, 	(member(X, Align_HypoCCGTerms), gen_quant_tt(X, List_TT)), 	List_Align_Hypos),
		% chosing random readings, not all
		at_most_n_random_members_from_list(List_Align_Prems, 5, List_Align_Prems_R),
		at_most_n_random_members_from_list(List_Align_Hypos, 5, List_Align_Hypos_R)
	  ; List_Align_Prems_R = [], % if 'no_align' then rturn empty lists
		List_Align_Hypos_R = []
	), !.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Produces a correct CCGTerm that needs type raising of the quatifiers
% in order to get final ttTerm
ccgTree_to_correct_ccgTerm(CCGTree, CCGTerm4) :-
	ccgIDTree_to_ccgIDTerm(ccg(_,CCGTree), ccg(_,CCGTerm1)),
	ne_ccg(CCGTerm1, CCGTerm2),
	clean_ccgTerm_once(CCGTerm2, CCGTerm3),
	correct_ccgTerm(CCGTerm3, CCGTerm4),
	( debMode('pr_lex_rules') ->
		print_used_lexical_rules('unexplained', CCGTerm4)
	  ; true
	).
