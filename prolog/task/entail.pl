%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- use_module('../prover/tableau_analysis').
%:- use_module('../knowledge/wn_preds').
:- use_module('../rules/rule_hierarchy', [set_rule_eff_order/0]).
:- use_module('../utils/user_preds', [
	prob_input_to_list/2, partition_list_into_N_even_lists/3,
	at_most_n_random_members_from_list/3,  print_prob/1, get_toks_annos/3,
	sen_id2anno/3
	]).
:- use_module('../utils/generic_preds', [ format_list/3, member_zip/2 ]).
:- use_module('../printer/conf_matrix', [draw_extended_matrix/2, draw_matrix/1]).
:- use_module('../printer/reporting', [report/1, pid_to_print_prob/2,
	write_predictions_in_file/1]).
:- use_module('../latex/latex_ttterm', [latex_probIDs_trees/2]).
:- use_module('../llf/recognize_MWE', [clean_ccgTerm_once/2]).
:- use_module('../llf/aligner', [align_ttTerms/4]).
:- use_module('../llf/gen_quant', [once_gen_quant_tt/2, gen_quant_tt/2]).
:- use_module('../llf/ccg_term', [ccgIDTree_to_ccgIDTerm/2, ccgIDTree_to_ccgIDTerm/3]).
:- use_module('../llf/correct_term', [correct_ccgTerm/2]).
:- use_module('../llf/ner', [ne_ccg/2]).
:- use_module('../llf/ttterm_preds', [
	ttTerms_same_type/2, lex_norm_ttterms/4
	]).
:- use_module('../llf/ttterm_to_term', [ttTerm_to_pretty_atom/2]).
:- use_module('../knowledge/ind_kb', [add_ind_kb/2, induced_rel/1]).
:- use_module('../knowledge/knowledge', [close_kb/3]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% entailment with the first GQTT
prove_nli :- prove_nli(_).

prove_nli(PIDs) :- prove_nli(PIDs, 'both').

prove_nli(PIDs, Align) :- prove_nli(PIDs, Align, []).

prove_nli(PIDs, Align, IKB) :-
		prove_nli(PIDs, Align, IKB, ['yes', 'no', 'unknown']).

prove_nli(List_Int, Align, IKB, List_of_Answers) :-
	% detecting problem IDs
	prob_input_to_list(List_Int, L1),
	( debMode('singPrem') ->
		findall(X, (member(X,L1), \+findall(_, sen_id(_,X,'p',_,_),[_,_|_])), L2 )
	; L2 = L1
	),
	( debMode('fracFilter') ->
		findall(X, (member(X,L2), \+member(X, [12,16,61,62,77,78,213,276,305,308,309,310])), List )
	; List = L2
	),
	% further filtering problem IDs
	findall((PID, Answer), (
		member(PID, List),
		sen_id(_, PID, h, Answer, _),
		memberchk(Answer, List_of_Answers)
	), PID_Ans),% to descard ill-problems of SNLI
	% list_to_set(ProbIds_Answers, PID_Ans),
	set_rule_eff_order, % defines an effciency order of rules
	( debMode('proof_tree') -> true; retractall(debMode('proof_tree'))),
	( debMode(parallel(_)) ->
		%concurrent_maplist(solve_entailment(Align), PID_Ans, Results)
		parallel_solve_entailment(Align, IKB, PID_Ans, Results)
	; maplist(solve_entailment(Align, IKB), PID_Ans, Results)
	),
	write_predictions_in_file(Results),
	draw_extended_matrix(Results, _Scores).

% bad fracas 12,16,61,62,77,78,213,276,305,308,309,310

% entailment with all GQTTs
% list_entail_all :-
% 	findall( (Problem_Id, Answer),
% 		sen_id(_, Problem_Id, _, Answer, _),
% 		ProbIds_Answers),
% 	list_to_set(ProbIds_Answers, ProblemIds_Answers),
% 	( debMode('proof_tree') -> true; retractall(debMode('proof_tree'))),
% 	maplist(list_solve_entailment, ProblemIds_Answers, Results),
% 	%draw_matrix(Results).
% 	draw_extended_matrix(Results, _Scores).


% list_entail_some(List) :-
% 	findall( (Problem_Id, Answer),
% 		( member(Problem_Id, List), sen_id(_, Problem_Id, _, Answer, _) ),
% 		ProbIds_Answers),
% 	list_to_set(ProbIds_Answers, ProblemIds_Answers),
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
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
solve_entailment(Align, IKB, (Id, Answer), (Id, Ans, Provers_Ans, Closed, Status) ) :-
	( Answer = 'undef' ->
		Ans = 'unknown'
	  ; Ans = Answer
	),
	%( debMode('2class') ->
	%	entail_2(Id, Ans, Provers_Ans, XP, Closed, Status);
	( debMode('shallow') ->
		shallow_reasoning(Id, Provers_Ans, XP, Closed, Status)%,  Closed = 'closed'
	; entail(Align, IKB, Id, Ans, Provers_Ans, XP, Closed, Status)
	),
	term_to_atom(Status, AtomStatus),
	( ( debMode('prprb'); Provers_Ans \= Ans ) ->
		pid_to_print_prob(Id, Prob)
	; Prob = '' ),
	format('~t~w:~5+~t [~w],~11+~t~w,~9+~t~w,~9+ ~w~t~12+ XP: ~w~w~n', [Id, Ans, Provers_Ans, Closed, AtomStatus, XP, Prob]).

solve_entailment( Align, (Id, Answer), (Id, Ans, Provers_Ans, Closed, Status) ) :-
	% by default initial KB is empty
	solve_entailment(Align, [], (Id, Answer), (Id, Ans, Provers_Ans, Closed, Status)).

%----------------------------------------------
% parallel version of solve_entailment
parallel_solve_entailment(Align, ProblemIds_Answers, Results) :-
	% drop binning as it is not significant for performance
	% concurrent_maplist(solve_entailment(Align), ProblemIds_Answers, Results).
	parallel_solve_entailment(Align, [], ProblemIds_Answers, Results).

parallel_solve_entailment(Align, KB, ProblemIds_Answers, Results) :-
	concurrent_maplist(solve_entailment(Align, KB), ProblemIds_Answers, Results).

/*
parallel_solve_entailment(Align, KB, ProblemIds_Answers, Results) :-
	debMode(parallel(Cores)),
	partition_list_into_N_even_lists(ProblemIds_Answers, Cores, JobList),
	length(JobList, JobNumber),
	% report Job partition
	report(['Number of jobs: ', JobNumber]),
	maplist(length, JobList, ListJobLength),
	atomic_list_concat(ListJobLength, ', ', JobMessage),
	report(['Length of jobs: ', JobMessage]),
	% Run concurrent solver for all jobs at the same time and collect all the results in the end
	concurrent_maplist(solve_accu_job(Align, KB), JobList, ResultList),
	partition_list_into_N_even_lists(Results, _, ResultList)
*/

solve_accu_job(Align, KB, ProblemIds_Answers, Results) :-
	maplist(solve_entailment(Align, KB), ProblemIds_Answers, Results).

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
check_problem(KB_XP, Prem_TTterms, Hypo_TTterms, 'yes', Provers_Ans, Closed, Status, BrList, Tree) :-
	!,
	( generateTableau(KB_XP, Prem_TTterms, Hypo_TTterms, BrList, Tree, Status) ->
		( BrList = [] ->
			Closed = 'closed', Provers_Ans = 'yes'
		;	Closed = 'open',   Provers_Ans = 'unknown'
		)
	; 	Closed = 'NA',
		Provers_Ans = 'unknown',
		Status = 'Defected'
	).

check_problem(KB_XP, Prem_TTterms, Hypo_TTterms, 'no_unk', Provers_Ans, Closed, Status, BrList, Tree) :- %Wrong
	!,
	check_problem(KB_XP, Prem_TTterms, Hypo_TTterms, 'yes', Provers_Ans, Closed, Status, BrList, Tree).

check_problem(KB_XP, Prem_TTterms, Hypo_TTterms, 'no', Provers_Ans, Closed, Status, BrList, Tree) :-
	!,
	append(Prem_TTterms, Hypo_TTterms, TTterms),
	( generateTableau(KB_XP, TTterms, [], BrList, Tree, Status) ->
		( BrList = [] ->
			Closed = 'closed', Provers_Ans = 'no'
		;	Closed = 'open',   Provers_Ans = 'unknown'
		)
	; 	Closed = 'NA',
		Provers_Ans = 'unknown',
		Status = 'Defected'
	).

check_problem(KB-XP, Prem_TTterms, Hypo_TTterms, 'unknown', Provers_Ans, Closed, Status, _, _) :-
	!,
	check_problem(KB-XP_yes, Prem_TTterms, Hypo_TTterms, 'yes', Provers_Ans_yes, Closed_yes, Status_yes, _BrList1, _Tree1),
	check_problem(KB-XP_no, Prem_TTterms, Hypo_TTterms, 'no', Provers_Ans_no, Closed_no, Status_no, _BrList2, _Tree2),
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
solve_problem(PrId_Al, KB-XP, Prem_TTterms, Hypo_TTterms, Prover_Ans, Closed, Status) :-
	check_problem(KB-XP_yes, Prem_TTterms, Hypo_TTterms, 'yes', _, Closed_yes, Status_yes, Br_yes, Tree_yes),
	check_problem(KB-XP_no, Prem_TTterms, Hypo_TTterms, 'no', _,  Closed_no, Status_no, Br_no, Tree_no),
	% write tableau proofs if needed
	add_to_stream('branches', ([PrId_Al, 'yes'], Br_yes)),
	add_to_stream('branches', ([PrId_Al, 'no'], Br_no)),
	( (Closed_yes, Closed_no) == ('closed', 'closed') ->
		report(['Warning: CONTRADICTION and ENTAILMENT at the same time: so NEUTRAL']),
		append(XP_yes, XP_no, XP),
		(Prover_Ans, Closed, Status) = ('unknown', 'open', 'Terminated')%,  %!!!
		%report_theUsedrules_in_tree(Tree_yes),
		%report_theUsedrules_in_tree(Tree_no)
	; (Closed_yes, Closed_no) == ('closed', 'open') ->
		(Prover_Ans, Closed, Status, XP)  = ('yes', Closed_yes, Status_yes, XP_yes),
		( theUsedrules_in_tree(Tree_yes, [H|T]) -> report([PrId_Al, ': ', [H|T]]); true )
	; (Closed_yes, Closed_no) == ('open', 'closed') ->
		(Prover_Ans, Closed, Status, XP)  = ('no', Closed_no, Status_no, XP_no),
		( theUsedrules_in_tree(Tree_no, [H|T]) -> report([PrId_Al, ': ', [H|T]]); true )
	; (Closed_yes, Closed_no) == ('open', 'open') ->
		Status_yes = (_,Steps1),
		Status_no  = (_,Steps2),
		Steps is Steps1 + Steps2,
		( (Status_yes = ('Lim',_); Status_no = ('Lim',_)) ->
			Status = ('Lim',Steps)
	  	  ; Status = ('Ter',Steps)
		),
		(Prover_Ans, Closed, XP)  = ('unknown', 'open', [])%,
		%report_theUsedrules_in_tree(Tree_yes),
		%report_theUsedrules_in_tree(Tree_no)
   	; (Closed_yes == 'NA'; Closed_no == 'NA') ->
		(Prover_Ans, Closed, Status, XP)  = ('unknown', 'NA', 'Defected', [])
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

% checks an LLF on contingency: whether it can be true or false
contingency_check(TF, KB, LLF) :-
	contingency_check(false, TF, KB, LLF, _Closed).

contingency_check(Verbose, TF, KB, LLF, Closed) :-
	memberchk(TF-P-H-Status, [true-[LLF]-[]-inconsistent, false-[]-[LLF]-valid]),
	check_problem(KB-_, P, H, 'yes', _, Closed, _, _, _),
	( Closed == 'closed' ->
		( Verbose ->
			ttTerm_to_pretty_atom(LLF, Term),
			report(['Warning: ', Status, ' LLF ', Term, '\n']),
			fail
		; fail )
	; true ).
	% memberchk((Closed, Answer), [('open','Consistent'), ('closed','Inconsistent'), ('NA', 'Defected')]).

% Depreciated. checks an LLF on consistency, faisl if it is not consistent
consistency_check(KB_XP, LLF, Answer) :-
	check_problem(KB_XP, [LLF], [], 'yes', _PrAns, Closed, _Status, _BrList, _Tree),
	%ignore(greason(KB, [LLF], [], 1)), % testing sentences separetly
	% add_to_stream(branches, (PrId-'consistency', BrList)),
	memberchk((Closed, Answer), [('open','Consistent'), ('closed','Inconsistent'), ('NA', 'Defected')]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
entail(Align, Id, Answer, Provers_Answer, XP, Closed, FinalStatus) :-
	% by default with empty initial KB
	entail(Align, [], Id, Answer, Provers_Answer, XP, Closed, FinalStatus).
%/*
% solves problems - doesnt knows the answer beforehand
entail(Align, IKB, Id, _Answer, Pred, XP, Cl, Status) :-
	% start tracing a particular problem
	( debMode(gtraceProb(Id)) -> gtrace, true; true ),
	nonvar(Align),
	findall(_X, sen_id(_, Id, _, _, _), Prem_Hyp), % finds the length of the problem
	%problem_id_TTterms(Id, P_TTs, H_TTs), AP_TTs = P_TTs, AH_TTs = H_TTs,
	( problem_to_ttTerms(Align, Id, P_TTs, H_TTs, AP_TTs, AH_TTs, OKB) ->
		append(IKB, OKB, KB), % merge initial and obtained KBs
		append(P_TTs, H_TTs, LLFs),
		( ttTerms_same_type(LLFs, _Type) ->
			( debMode('constchk'),
			  \+( ( maplist(contingency_check(true, KB), LLFs)
				  %; maplist(contingency_check(false, KB), LLFs)
				  ) ) ->
				(Pred, Cl, Status, XP) = ('unknown', 'NA', 'Defected', [])
			; align_solve_problem(Align, KB, Id, Prem_Hyp, P_TTs, H_TTs, AP_TTs, AH_TTs, Pred, XP, Cl, Status)
			)
		; report(['Inconsistency in node types (entail/8)']),
			(Pred, Cl, Status) = ('unknown', 'NA', 'Defected')
		)
	; report(['Failed to get ttTerms (entail/8)']),
		(Pred, Cl, Status) = ('unknown', 'NA', 'Defected')
	).

% solve a problem which has well-formed and consistent LLFs
% while solving take into account alignment flag
align_solve_problem('align', KB, Id, _, _, _, AP_TTs, AH_TTs, Pred, XP, Cl, Status) :-
	solve_problem(Id-'align', KB-XP, AP_TTs, AH_TTs, Pred, Cl, Status).

align_solve_problem('no_align', KB, Id, _, P_TTs, H_TTs, _, _, Pred, XP, Cl, Status) :-
	solve_problem(Id-'no_align', KB-XP, P_TTs, H_TTs, Pred, Cl, Status).

align_solve_problem('both', KB, Id, P_H, P_TTs, H_TTs, AP_TTs, AH_TTs, Pred, XP, Cl, Status) :-
	solve_problem(Id-'no_align', KB-XP_N, P_TTs, H_TTs, Pred_N, Cl_N, Status_N),
	solve_problem(Id-'align', KB-XP_A, AP_TTs, AH_TTs, Pred_A, Cl_A, Status_A),
    ( Cl_A \== 'closed', Cl_N \== 'closed', \+append(P_TTs, H_TTs, P_H) ->
		% if an item in the problem is defected
		(Pred, XP, Cl, Status) = ('unknown', [], 'NA', 'Defected')
	; Cl_A == 'closed' ->
		(Pred, XP, Cl, Status) =  (Pred_A, XP_A, Cl_A, Status_A)
	; (Pred, XP, Cl, Status)   =  (Pred_N, XP_N, Cl_N, Status_N)
	).



% true if TTs are compatible
% Helps to guess the kind of conjunction duirng proving
compatible_TTconcepts(TTs, KB) :-
	generateTableau(KB-_, TTs, [], BrList, _, _) ->
		BrList \= []
	; format('WARNING: compatibility check failed: ~w~n', [TTs]).

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
	gentail(Align, [], Problem_Id).

gentail(Align, KB0, Problem_Id) :-
	set_rule_eff_order, % defines an effciency order of rules
	once(sen_id(_, Problem_Id, _, Answer, _)),
	%problem_id_TTterms(Problem_Id, Prem_TTterms, Hypo_TTterms),
	( Align == 'align' ->
		problem_to_ttTerms(Align, Problem_Id, _, _, Prem_TTterms, Hypo_TTterms, KB1)
	  ; problem_to_ttTerms('no_align', Problem_Id, Prem_TTterms, Hypo_TTterms, _, _, KB1)
	),
	append(KB0, KB1, KB01),
	list_to_ord_set(KB01, KB),
	append(Prem_TTterms, Hypo_TTterms, TTterms),
	atomic_list_concat(['LLF_Prob-', Problem_Id], FileName),
	( debMode('tex') -> latex_probIDs_trees([Problem_Id], FileName); true ),
	( Prem_TTterms = [], Hypo_TTterms = [] ->
		writeln('Problem with this id plausibly does not exist!')
	; Prem_TTterms = [] ->
		writeln('No premises found for this problem!')
	; Hypo_TTterms = [] ->
		writeln('No hypothesis found for this problem!')
	;	% Reason! problem is ok
	  Answer = 'no' ->
		greason(KB-XP, TTterms, [], [Problem_Id, 'no', Align])
	; Answer = 'yes' ->
		greason(KB-XP, Prem_TTterms, Hypo_TTterms, [Problem_Id, 'yes', Align])
	; greason(KB-XP, Prem_TTterms, Hypo_TTterms, [Problem_Id, 'yes', Align]) ->
		true
	; greason(KB-XP, TTterms, [], [Problem_Id, 'no', Align])
	),
	format('XP: ~w~n', [XP]).

% TODO: remove redundancy from this predicate
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% doesnt take into account answer of the problem
gentail_no_answer(Problem_Id) :-
	gentail_no_answer('no_align', Problem_Id).

gentail_no_answer(Align, Problem_Id) :-
	gentail_no_answer(Align, [], Problem_Id).

gentail_no_answer(Align, KB0, Problem_Id) :-
	set_rule_eff_order, % defines an effciency order of rules
	once(sen_id(_, Problem_Id, _, Answer, _)),
	%problem_id_TTterms(Problem_Id, Prem_TTterms, Hypo_TTterms),
	( Align == 'align' ->
		problem_to_ttTerms(Align, Problem_Id, _, _, Prem_TTterms, Hypo_TTterms, KB1)
	  ; problem_to_ttTerms('no_align', Problem_Id, Prem_TTterms, Hypo_TTterms, _, _, KB1)
	),
	append(KB0, KB1, KB01),
	list_to_ord_set(KB01, KB),
	atomic_list_concat(['LLF_Prob-', Problem_Id], FileName),
	( debMode('tex') -> latex_probIDs_trees([Problem_Id], FileName); true ),
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
		greason(KB-XP, TTterms, [], [Problem_Id, 'no', Align])
	; Answer = 'yes' ->
		ignore(greason(KB-_, TTterms, [], [Problem_Id, 'no', Align])),
		greason(KB-XP, Prem_TTterms, Hypo_TTterms, [Problem_Id, 'yes', Align])
	; greason(KB-XP, Prem_TTterms, Hypo_TTterms, [Problem_Id, 'yes', Align]) ->
		true
	; %append(Prem_TTterms, Hypo_TTterms, TTterms),
	  greason(KB-XP, TTterms, [], [Problem_Id, 'no', Align])
	),
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
	( debMode('tex') -> latex_probIDs_trees([Problem_Id], FileName); true ),
	append(Prem_TTterms, Hypo_TTterms, TTterms),
	( Sign = 'true' ->
		greason(KB-XP, TTterms, [], Problem_Id)
	; Sign = 'false' ->
		greason(KB-XP, [], TTterms, Problem_Id)
	),
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
	ccgIDTree_to_ccgIDTerm(ccg(Id,CCGTree), ccg(Id,CCGTerm1)),
	ne_ccg(CCGTerm1, CCGTerm2),
	clean_ccgTerm_once(CCGTerm2, CCGTerm3),
	correct_ccgTerm(CCGTerm3, CCGTerm4),
	%gen_quant_tt(CCGTerm4, TTterms).
	once_gen_quant_tt(CCGTerm4, TTterm).

% Produces a list of all possible TTterms from a CCGTerm
ccgTree_to_TTterms(CCGTree, TTterms) :-
	ccgIDTree_to_ccgIDTerm(ccg(Id,CCGTree), ccg(Id,CCGTerm1)),
	ne_ccg(CCGTerm1, CCGTerm2),
	clean_ccgTerm_once(CCGTerm2, CCGTerm3),
	correct_ccgTerm(CCGTerm3, CCGTerm4),
	gen_quant_tt(CCGTerm4, TTterms).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
problem_to_ttTerms(Align, Prob_Id, Prems, Hypos, Align_Prems, Align_Hypos, KB) :-
	( debMode(gtraceProb(Prob_Id)) -> gtrace, true; true ),
	problem_to_corrected_terms(Prob_Id, PremCCGTerms1, HypoCCGTerms1),

	% extracting WN_relations for aligning
	append(PremCCGTerms1, HypoCCGTerms1, AllCCGTerms1),
	lex_norm_ttterms(llf_norm, AllCCGTerms1, AllCCGTerms, Lex),
	append(PremCCGTerms, HypoCCGTerms, AllCCGTerms),
	same_length(PremCCGTerms1, PremCCGTerms),

	( debMode('prlex') -> report([Lex]); true),
	( debMode('no_wn') -> KB0 = []; kb_from_wn(Lex, KB0) ), % extract relevant semantic relations from WN
	( debMode('ind_kb') -> add_ind_kb(KB0,KB1); KB1 = KB0 ),
	close_kb(Lex, KB1, KB),
	( debMode('pr_kb') -> report(['KB: ', KB1]); true ),
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
% Produces a correct CCGTerm that needs type raising of the quatifiers
% in order to get final ttTerm
ccgTree_to_correct_ccgTerm(CCGTree, Term) :-
	ccg(Id, CCGTree),
	sen_id_to_base_ttterm(Id, T),
	%ccgIDTree_to_ccgIDTerm(ccg(Id,CCGTree), ccg(Id,CCGTerm1), Annos),
	correct_ttterm(T, Term).

correct_ttterm(T, CorrT) :-
	ne_ccg(T, T1),
	clean_ccgTerm_once(T1, T2),
	correct_ccgTerm(T2, CorrT),
	( debMode('pr_lex_rules') ->
		print_used_lexical_rules('unexplained', CorrT)
	  ; true
	).

problem_to_corrected_terms(PID, CorrPTs, CorrHTs) :-
	findall(T, (
		sen_id(SID, PID, 'p', _, _),
		once(sen_id_to_base_ttterm(SID, T))
	), PTs),
	findall(T, (
		sen_id(SID, PID, 'h', _, _),
		once(sen_id_to_base_ttterm(SID, T))
	), HTs),
	append(PTs, HTs, Ts),
	lex_norm_ttterms('ccg_norm', Ts, NormTs, _Lex),
	append(NormPTs, NormHTs, NormTs), same_length(PTs, NormPTs),
	maplist(correct_ttterm, NormPTs, CorrPTs),
	maplist(correct_ttterm, NormHTs, CorrHTs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% :- multifile sen_id_to_base_ttterm/3.
% :- discontiguous sen_id_to_base_ttterm/3.
% :- multifile sen_id_to_base_ttterm/4.
% :- discontiguous sen_id_to_base_ttterm/4.

% Get TTterm for SIDth sentence that followws one of the available
% annotation layer->system combinations
sen_id_to_base_ttterm(SID, TTterm) :-
	once(sen_id2anno(SID, Tree, DetAnno)),
	ccgIDTree_to_ccgIDTerm(ccg(SID,Tree), ccg(SID,TTterm), DetAnno).
