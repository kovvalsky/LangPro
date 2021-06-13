%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Induction of lexical relations from an open tableau
% which cause the tableu to close according to the gold answer
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%:- ensure_loaded(['../knowledge/induced_kb'
%				 ]).

:- use_module('../rules/rules', [op(610, xfx, ===>)]).
:- use_module('../printer/reporting', [
	report/1, par_format/2, print_pre_hyp/2, report/2, print_pre_hyp/1
	]).
:- use_module('../lambda/lambda_tt', [op(605, yfx, @)]).
:- use_module('../utils/user_preds', [
	concurrent_maplist_n_jobs/3, %element_list_member/3,
	list_to_freqList/2, shared_members/2,
	sym_rels_to_canonical/2, prob_input_to_list/2,
	partition_list_into_N_even_lists/3,
	uList2List/2, prIDs_to_prIDs_Ans/2, get_value_def/3,
	average_list/2, all_prIDs_Ans/1]).
:- use_module('../utils/generic_preds', [
 	format_list/3, format_list_list/3, format_list_list/4, keep_smallest_lists/2,
	sublist_of_list/2, sort_list_length/2
	]).
:- use_module('../llf/ttterm_to_term', [ttTerm_to_prettyTerm/2]).
:- use_module(library(pairs)).
:- use_module('../prover/tableau_utils', [
	get_closure_rules/2
	]).
:- use_module('../utils/induction_utils', [
	add_lex_to_id_ans/2, filterAns_prIDs_Ans/3, format_pairs/2, get_IDAs/2,
	has_rel_against_kb/3, has_rel_incomparables/2, kb_length/2,
	log_parameters/1, print_learning_phase_stats/3,
	print_kb_learning_stages/3, print_phase_stats/4, partition_as_prIDs_Ans/6,
	print_learning_stages/2, write_induced_kb_in_file/3, waif_cv3/3
	]).
:- use_module('../printer/conf_matrix', [draw_extended_matrix/2]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% when development or evaluation sets are unspecified they will be ignored
train_dev_eval_sick_parts((Tccg,Tsen), (Dccg,Dsen), (Eccg,Esen), Config) :-
	log_parameters(Config),
	waif_cv3(TFile, DFile, EFile),
	% load and train on train set
	load_ccg_sen_probs(Tccg, Tsen, TPIDA),
	%retractall(debMode('ind_kb')),
	train_with_abduction(Config, TPIDA, KB, T_Scores, T_Acc),
	format('~`=t Learned Knowledge ~`=t~80|~n', []),
	maplist(writeln, KB),
	% write knowledge
	( debMode(waif(FileName)) ->
		format(atom(KBFile), '~w_KB.pl', [FileName]),
		write_induced_kb_in_file(KB, KBFile, Config)
	; true ),
	(atom(Tccg), atom(Tsen) -> unload_file(Tccg), unload_file(Tsen); true ),
	% pedict on train set
	evaluate_on_portion(Config, KB, (Tccg,Tsen), TFile, TAPR),
	% load and predict on dev set
	( nonvar(Dccg), nonvar(Dsen) ->
		evaluate_on_portion(Config, KB, (Dccg,Dsen), DFile, DAPR)
	; 	DAPR = [0,0,0]
	),
	% load and predict on evaluation set
	( nonvar(Eccg), nonvar(Esen) ->
		evaluate_on_portion(Config, KB, (Eccg,Esen), EFile, EAPR)
	; 	EAPR = [0,0,0]
	),
	% quick results
	format('Train on Train::: ~w; Acc: ~2f~n', [T_Scores, T_Acc]),
	format('Predict on Train::: Acc: ~2f; Prec: ~2f; Rec: ~2f~n', TAPR),
	format('Predict on Dev  ::: Acc: ~2f; Prec: ~2f; Rec: ~2f~n', DAPR),
	format('Predict on Eval ::: Acc: ~2f; Prec: ~2f; Rec: ~2f~n', EAPR).

tde_sick_part(Tccg, Tsen, Config) :-
	train_dev_eval_sick_parts((Tccg,Tsen), (Tccg,Tsen), (Tccg,Tsen), Config).

%------------------------------------
load_ccg_sen_probs(Parts, _, PIDAs) :-
	debMode(lang('nl')), !,
	retractall( debMode(parts(_)) ),
	assertz( debMode(parts(Parts)) ),
	all_prIDs_Ans(PIDAs).


load_ccg_sen_probs(CCG, SEN, PIDAs) :-
	ensure_loaded(CCG),
	ensure_loaded(SEN),
	%all_prIDs_Ans(PIDAs1), findall(P-A, (member(P-A, PIDAs1), between(1495,1500,P)), PIDAs).
	all_prIDs_Ans(PIDAs).
%------------------------------------

report_asserted_sen_ccg :-
	findall(0, ccg(_,_), CCG),
	findall(0, sen_id(_,_,_,_,_), Sen),
	length(CCG, NCCG),
	length(Sen, NSen),
	format("~w ccg/2 and ~w sen_id/5~n", [NCCG, NSen]).

%-------------------------------------
evaluate_on_portion(Config, KB, (CCG,SEN), File, APR) :-
	load_ccg_sen_probs(CCG, SEN, PIDA),
	retractall(debMode(waif(_))),
	assertz(debMode(waif(File))),
	predict_with_iKB(Config, KB, PIDA, [_, AccE, PrecE, RecE], _, _, _),
	(atom(CCG), atom(SEN) -> unload_file(CCG), unload_file(SEN); true ),
	APR = [100*AccE, 100*PrecE, 100*RecE].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Knowledge induction with 3-fold cross-validation.
% This is used to find the best settings for KB learning on small training data.
% leave Answers as _ to allow all answers.
cv_induce_knowledge(PrIDs, Answers, Config) :-
	log_parameters(Config),
	findall(TrAcc-TsAcc, (
		fold_induce_knowledge(Config, PrIDs, Answers, Index, _D, TrAcc, TsAcc),
		format('~n~n~t End of fold ~w ~t~50|~n', [Index]),
		format('~`=t~50|~n Train: ~2f; Test: ~2f ~n~`=t~50|~n~n', [TrAcc, TsAcc])
		), TrTsAs),
	maplist([A,B,A-B]>>true, TrAs, TsAs, TrTsAs),
	format('~`=t~50|~n', []),
	format_pairs(' Train: ~2f; Test: ~2f ~n', TrTsAs),
	average_list(TrAs, TrAv),
	average_list(TsAs, TsAv),
	format('~`=t~50|~nAve. Train: ~2f; Ave. Test: ~2f~n', [TrAv, TsAv]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% One fold, Index tracks the number of the fold
fold_induce_knowledge(Config, PrIDs, Answers, Index, Detailed, TrAcc, TsAcc) :-
	get_value_def(Config, 'fold', N),
	partition_as_prIDs_Ans(PrIDs, Answers, 990, N, AllParts, _CumDiff),
	select(Test, AllParts, TrainParts), % Leaves the choice point
	nth1(Index, AllParts, Test),
	append(TrainParts, Train),
	%while_improve_induce_prove(Train, _UnSolved, Align, Check, [], _List_of_Cnt_KB). % with no init KB
	train_test(Config, Train, Test, TrainInfo, TestInfo, TrAcc, TsAcc),
	Detailed = ['train'-TrainInfo, 'test'-TestInfo].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Train on the training set with abduction and use abduced knowledge for testing
train_test(Config, TrainPIDA, TestPIDA, TrainScores, TestScores, TrAcc, TsAcc) :-
	train_with_abduction(Config, TrainPIDA, KB, TrainScores, TrAcc),
	predict_with_iKB(Config, KB, TestPIDA, [_Total, Acc, Prec, Rec], TsAcc, _, _),
	format(atom(TestScores), '~2f ~2f ~2f', [Acc, Prec, Rec]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Induce knowledge as long as it boosts the performace
train_with_abduction(Config, TrainIDA, Induced_KB, TrainScores, TrAcc) :-
	% base case: evaluate the prover on the data without any induced knowledge
	concurrent_maplist_n_jobs(add_lex_to_id_ans, TrainIDA, TrainIDAL),
	predict_with_iKB(Config, [], TrainIDAL, _, _Acc, SolvA0, FailA0),
	% Try now if knowledge induction improves over the base case. Start with no initial KB
	while_improve_induce_prove(TrainIDAL, FailA0-FailA, SolvA0-SolvA, Config, [], Induced_KB0),
	maplist(length, [TrainIDAL, FailA, SolvA], [A, F, S]),
	format(atom(TrainScores), '~2f ~2f', [100*S/A, 100*F/A]), % Accuracy and error rate
	%append(List_of_Cnt_KB, Cnt_KB),
	%maplist([X,Y,X-Y]>>true, _, KB0, Cnt_KB),
	sort(0, @>, Induced_KB0, Induced_KB),
	TrAcc is 100*S/A.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Evaluate prover on the list of pID,Ans[,Lex] using the induced knowledge
predict_with_iKB(Config, IKB, IDALs, Score_List, Acc, SolvedA, FailedA) :-
	get_value_def(Config, 'align', Align),
	get_IDAs(IDALs, IDAs),
	( debMode(parallel(_)) -> parallel_solve_entailment(Align, IKB, IDAs, Results)
	; maplist(solve_entailment(Align, IKB), IDAs, Results)),
	findall((ID,A), member((ID,A,A,_,_), Results), SolvedA),
	findall((ID,A), ( member((ID,A,P,_,_), Results), A \= P ), FailedA),
	draw_extended_matrix(Results, Score_List),
	Score_List = [_Total, Acc_|_],
	Acc is Acc_ * 100.

assert_induced_rel(Rel) :-
	assertz(induced_rel(Rel)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Given a list of problems (leave as _ to get all problems)
% with possibly specified list of answers (e.g., [yes] picks only entailment problems),
% loop over the problems and induce KB untill it is not possible
induce_knowledge(ToSolve, Answers, UnsolvedProbIDs, Config, KB) :-
	log_parameters(Config),
	prob_input_to_list(ToSolve, ToSolveList),
	% augment problems with answers
	prIDs_to_prIDs_Ans(ToSolveList, ToSolveList_Ans),
	% filter the prob-ans pairs based on the answer set
	filterAns_prIDs_Ans(ToSolveList_Ans, Answers, ToSolve_Ans),
	while_improve_induce_prove(_IDALs, ToSolve_Ans-Failed1, []-Solved1, Config, [], List_of_Cnt_KB), % with no init KB
	maplist([A,B,A-B]>>true, UnsolvedProbIDs, _, Failed1),
	print_kb_learning_stages(List_of_Cnt_KB, Cnt_KB_srt, KB),
	% write knowledge in a file
	( debMode(waif(FileName)) -> write_induced_kb_in_file(Cnt_KB_srt, FileName, Config); true ),
	append(Failed1, Solved1, All),
	maplist(length, [All, Solved1, Failed1], [N, S1, F1]),
	format('~`=t Acc (~2f%); Total (~w); Solved (~w); Failed (~w) ~`=t~100|~n~`=t~100|~n', [100*S1/N, N, S1, F1]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Loop over the problems and induce the KB gradually:
% prove problems and induce kb from proved ones, then reuse the induced kb
% for proving & inducing new kb from the rest of the unproved problems
% ToSolve_Ans = Solved_Ans + UnSolved_Ans, all these are lists of problemID-Ans pairs
while_improve_induce_prove(IDALs, FailA0-FailA, SolvA0-SolvA, Config, Init_KB, Induced_KB) :-
	maplist(length, [IDALs, SolvA0, FailA0], [N, S0, F0]),
	format('~`=t Acc (~2f%); Total (~w); Solved (~w); Failed (~w) ~`=t~80|~n~`=t~80|~n', [100*S0/N, N, S0, F0]),
	kb_induction_all(Config, IDALs, SolvA0, Init_KB, Ind_KB),
	( Ind_KB == [] -> Gain = 0
	; append(Init_KB, Ind_KB, Init_KB1),
		predict_with_iKB(Config, Init_KB1, IDALs, _, _, SolvA1, FailA1),
		print_learning_phase_stats(FailA0-FailA1, SolvA0-SolvA1, Ind_KB),
		length(SolvA1, S1),
		Gain is S1 - S0 ),
	( Gain =< 0 ->
		format('~`=t~80|~nNo improvement (~w). Stop!~n~`=t~80|~n', [Gain]),
		FailA = FailA0, % take the old values as the found KB is harmful and not retained
		SolvA = SolvA0,
		Induced_KB = [] % add no new Knowledge as it is harmful
	; format('~`=t~80|~nImprovement (~w). Continue~n~`=t~80|~n', [Gain]),
		%maplist([X,Y,X-Y]>>true, _, KB, Cnt_Facts0),
		while_improve_induce_prove(IDALs, FailA1-FailA, SolvA1-SolvA, Config, Init_KB1, Rest_Ind_KB),
		append(Ind_KB, Rest_Ind_KB, Induced_KB)
	).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Induce knowledge
kb_induction_all(Config, IDALs, SolvA, Init_KB, Ind_KB) :-
	% for effciency solved examples can be omitted for induction
	get_IDAs(IDALs, IDAs),
	subtract(IDAs, SolvA, Unsolv_IDAs),
	par_kb_induction_some(Config, Init_KB, Unsolv_IDAs, LL_KB, Info5),
	% Get a new list of failed problems
	findall((PrID,Ans), member([PrID,Ans,'solved',_,_], Info5), Draft_SolvA),
	length(Draft_SolvA, Draft_S), length(SolvA, S),
	format('~`-t Draft Results: solved ~w + ~w ~`-t~80|~n', [S, Draft_S]),
	% print counts of induced relations
	append(LL_KB, L_KB),
	list_to_freqList(L_KB, KB_cnts),
	transpose_pairs(KB_cnts, Cnt_KBs),
	format_list(atom(List), '    ~w~n', Cnt_KBs),
	format('~`-t Counts of Induced Relations ~`-t~50|~n~w~n', [List]),
	% filter out induced relations by keeping only harmless ones. Using all problems!
	exclude(=([]), LL_KB, LL_neKB),
	list_to_ord_set(LL_neKB, Potential_KBs),
	pick_harmless_KBs(Config, SolvA, IDALs, Potential_KBs, Ind_KB).


% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Pick only those KBs that doesn't hurt performance
pick_harmless_KBs(Config, SolvA, IDALs, L_KBs, Harmless_KB) :-
	% maplist(best_kb_wrt_data(Config, SolvA, IDALs), L_KBs, L_Best_KB_Score_SU),
	concurrent_maplist_n_jobs(best_kb_wrt_data(Config, SolvA, IDALs), L_KBs, L_Best_KB_Score_SU),
	sort([1,1,2], @>=, L_Best_KB_Score_SU, Ord_L_Best_KB_Score_SU),
	findall(KB, (
		member(KB-Sc-S-U, Ord_L_Best_KB_Score_SU),
		( Sc > 0 -> Ast = '+ '; Ast = '- '),
		format('~t~w~5| ~w ~w ~t~40+ Solved: ~w; Unsolved: ~w~n', [Sc, Ast, KB, S, U]),
		Ast == '+ ' % filter out harmful ones
	), KBs),
	append(KBs, Harmless_KB0),
	list_to_ord_set(Harmless_KB0, Harmless_KB).

%--------------------------------------------------
% Pick the best among the KB candidates induced from the same problem
best_kb_wrt_data(Config, SolvA, IDALs, KBs, Best_KB-Score-S-U) :-
	maplist(estimate_kb_wrt_data(Config, SolvA, IDALs), KBs, L_Score_SU_KB),
	sort(0, @>=, L_Score_SU_KB, Ord_L_Score_SU_KB),
	Ord_L_Score_SU_KB = [MaxSc-_-_-_|_],
	% keep KBs with max score & pick those with shortest relations
	findall(X, (
		member(X, Ord_L_Score_SU_KB), X = MaxSc-_-_-_
	), L_MaxSc_SU_KB),
	maplist([Head-KB, Head-KB-L]>>kb_length(KB, L),
		L_MaxSc_SU_KB, L_MaxSc_SU_KB_Len),
	sort(2, @=<, L_MaxSc_SU_KB_Len, [Score-S-U-Best_KB-_L | _]).
	%!!! there can be several KBs with same max score, but pick the first
	% 592 disj(put,reveal), disj(conceal,reveal)

%---------------------------------------------------
% Evaluate KB wrt data in terms of how many proofs it helps minus how many it harms
estimate_kb_wrt_data(Config, SolvA, IDALs, IKB, Score-Solv-Unsolv-IKB) :-
	% get word involved in KB
	maplist([(ID,_), ID]>>true, SolvA, SolvIDs_),
	list_to_ord_set(SolvIDs_, SolvIDs),
	% get lexical units for each rel of each KB: [disj('black dog', 'white cat')] -> [black,...,cat]
	findall(List_AB, (
		member(Rel,IKB), Rel=..[_,A,B],
		atomic_list_concat(List_A, ' ', A),
		atomic_list_concat(List_B, ' ', B),
		append(List_A, List_B, List_AB)
	), L_KB_Lex_Units),
	% verify KB's contribution for each problem in data and calculate overall contribution
	maplist(estimate_kb_wrt_prob(Config, IKB, L_KB_Lex_Units), IDALs, L_Solv, L_Unsolv),
	append(L_Solv, Solv0), list_to_ord_set(Solv0, Solv1),
	append(L_Unsolv, Unsolv0), list_to_ord_set(Unsolv0, Unsolv1),
	ord_subtract(Solv1, SolvIDs, Solv),
	ord_intersection(SolvIDs, Unsolv1, Unsolv),
	length(Solv, S), length(Unsolv, U), Score is S - U.

% Evaluate KB wrt a single problem
estimate_kb_wrt_prob(Config, IKB, L_KB_Lex_Units, (ID,Ans,Lex), Solv, Unsolv) :-
	member(KB_Lex_Units, L_KB_Lex_Units),
	sublist_of_list(KB_Lex_Units, Lex),
	!,
	get_value_def(Config, 'align', Align),
	entail(Align, IKB, ID, Ans, Pred, _, _, _),
	( Ans == Pred ->
		(Solv, Unsolv) = ([ID], [])
	; (Solv, Unsolv) = ([], [ID])
	).

estimate_kb_wrt_prob(_Config, _IKB, _L_KB_Lex_Units, (_,_,_Lex), [], []).




%-----------------------------------------------
% Predicate specially tailored for concurrent_maplist

% Parallel mode
par_kb_induction_some(Config, Init_KB, IDAs, KBs, Info5) :-
	debMode(parallel(Cores)),
	!,
	partition_list_into_N_even_lists(IDAs, Cores, JobList),
	concurrent_maplist(kb_induction_some(Config,Init_KB), JobList, List_of_KBs, List_of_Stats_Ans),
	partition_list_into_N_even_lists(KBs, Cores, List_of_KBs),
	partition_list_into_N_even_lists(Info5, Cores, List_of_Stats_Ans).

% Non-parallel mode
par_kb_induction_some(Config, Init_KB, IDAs, KBs, Info5) :-
	kb_induction_some(Config, Init_KB, IDAs, KBs, Info5).

% Auxiliary for maplist
kb_induction_some(Config, Init_KB, IDAs, LL_KB, Info5) :-
	maplist(kb_induction_prob(Config,Init_KB), IDAs, LL_KB, Info5).
	% findall(KB, (
	% 	member(L_KB, LL_KB),
	% 	( L_KB=[] -> KB=[]; L_KB=[KB|_] ) %!!! pick only the first KB candidate
	% 	), KBs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Induce knowledge from a single problem
% This prints rarely when the parallel mode is on
kb_induction_prob(Config, KB0, (PrId,Ans), L_KB, Info) :-
	get_value_def(Config, 'align', Align),
	( prepare_ttTerms_KB(PrId, Align, KB0, PTT-HTT, AlPTT-AlHTT, KB1) ->
		build_discover((PrId,Ans), Config, KB1, PTT-HTT, AlPTT-AlHTT, L_KB, Info)
	; Info = [PrId, Ans, 'failed', 'Failed to get TT-terms', 'defected'] ),
	!,
	par_format('~t~w~6| [~w]-~w: ~w (~w)~n', Info),
	par_format('~`-t~50|~n', []).

% HACK find out if this happens
kb_induction_prob(_Config, _KB0, _PrIdAs, _, _Stat_Ans) :-
	format('??? This should not happen!'),
	fail.

build_discover((PrId,Ans), Config, KB, PTT-HTT, AlPTT-AlHTT, L_KB, Info) :-
	get_value_def(Config, 'align', 'both'), !,
	% for both build non_align first, then align if needed
	% note that these examples are unsolvable at this point,
	% so proving with aligned ones first is not efficient
	get_branches(Ans, 'no_align', KB, PTT-HTT, AlPTT-AlHTT, TTs1, Brs1, St1),
	discover_knowledge(Config, TTs1, Brs1, KB, (PrId,Ans), St1, L_KB1, Info1),
	Info1 = [_,_,Solved,_,_],
	( (Solved == 'solved'; L_KB1 \= []) -> % preference to KB for non_align LLFs
	  (L_KB, Info) = (L_KB1, Info1)
	; get_branches(Ans, 'align', KB, PTT-HTT, AlPTT-AlHTT, TTs2, Brs2, St2),
	  discover_knowledge(Config, TTs2, Brs2, KB, (PrId,Ans), St2, L_KB2, Info2),
	  (L_KB, Info) = (L_KB2, Info2) ).

build_discover((PrId,Ans), Config, KB, PTT-HTT, AlPTT-AlHTT, L_KB, Info) :-
	get_value_def(Config, 'align', Align), !,
	get_branches(Ans, Align, KB, PTT-HTT, AlPTT-AlHTT, TTs, Brs, St),
	discover_knowledge(Config, TTs, Brs, KB, (PrId,Ans), St, L_KB, Info).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Discoveres knowledge from an open tableau (i.e. brancehs)
% Specify a list of patterns that describe the terms in discovered knowledge

discover_knowledge(_Config, _TTterms, _, _KB1, (PrId,Ans), 'defected', [], Info5) :-
	!,
	Info5 = [PrId, Ans, 'failed', 'Inconsistent types', 'defected'].

% When tableau is closed, do nothing
discover_knowledge(_Config, _TTterms, Branches, _KB1, (PrId,Ans), Status, [], Info5) :-
	Branches == [], % to avoid leackage
	!,
	( memberchk(Ans, ['yes', 'no']) -> %!!! what about fasle proofs?
		Solved = 'solved'
	;	Solved = 'failed'
	),
	Info5 = [PrId, Ans, Solved, 'closed', Status].


% When gold label is unknown, do nothing
discover_knowledge(_Config, _TTterms, [_|_], _KB1, (PrId,'unknown'), Status, [], Info5) :-
	!,
	Info5 = [PrId, 'unknown', 'solved', 'open', Status].

% When gold label in yes|no and tablea is open, do abduction
discover_knowledge(Config, TTterms, Branches, KB1, (PrId,Ans), Status, Learned_KBs, Info5) :-
	% patterns of inspected LLFs
	( get_value_def(Config, 'patterns', Patterns), is_list(Patterns) -> true
	% by default, if not specified, patterns with upto 3 terms are used
	; Patterns = [_, _@_, (_@_)@_, _@(_@_)]	),
	discover_patterned_knw(Config, TTterms, Branches, KB1, Patterns, Learned_KBs),
	( Learned_KBs = []
	->	Info5 =  [PrId, Ans, 'failed', 'open', Status]
	; 	Info5 =  [PrId, Ans, 'solved', 'closed', Status],
		format_list_list(atom(KBprint), '    ~w~n', '~w  ', Learned_KBs),
		print_pre_hyp(atom(Problem), PrId),
		format('~w!!! Possible KBs:~n~w~t~w~8| [~w]-~w: ~w (~w)~n', [Problem, KBprint | Info5])
	).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Learned_KBs is a list of KBs (sorted according to the size asc)
% where each of the KB can close the tableau
discover_patterned_knw(Config, TTterms, Branches, IniKB, Patterns, Learned_KBs) :-
	% Get relevant closure rules based on the lexicon extacted from Terms
	extract_lex_NNPs_ttTerms(TTterms, Lexicon, _Names),
	get_closure_rules(Lexicon, ClRules),
	% Following the patterns of nodes, find all possible KBs that closes the tableau
	maplist( pattern_filtered_nodes(Patterns), Branches, FilteredBranches ),
	findall(L_KB, ( % a list of sets of facts, that can close Branch
		member(Br, FilteredBranches),
		all_closing_KB(ClRules, Br, IniKB, L_KB) % K is a list of lists (of relations)
		), LL_KB), % a list of lists of lists (of relations)
	shared_members(L_ClKB, LL_KB),
	% From found Closing KBs, select good ones that are compatible with Initial KB, IniKB
	get_value_def(Config, 'constKB', ConstKB),
	get_value_def(Config, 'compTerms', CompTerms),
	findall(ClKB, (
		member(ClKB, L_ClKB),
		\+((has_rel_against_kb(ClKB, Lexicon, IniKB), ConstKB)),
		\+((has_rel_incomparables(ClKB, Lexicon), CompTerms))
		), L_goodClKB),
	sort(L_goodClKB, Ord_goodClKB),
	% Discard those KBs that require more assumptions. So if there is KB0 < KB1, remove KB1
	keep_smallest_lists(Ord_goodClKB, Abduced_L_KB), %!!! have a look
	% Discard those KBs that make any sentence inconsistent
	get_value_def(Config, 'constchk', ConstCheck),
	( ConstCheck ->
		findall(K, (
			member(K, Abduced_L_KB),
			maplist(consistency_check(K-_XP), TTterms, Checks),
			\+memberchk('Inconsistent', Checks)
		), Cnst_Abd_L_KB)
	; Cnst_Abd_L_KB = Abduced_L_KB
	),
	sort_list_length(Cnst_Abd_L_KB, Learned_KBs).
	%term_to_atom(IniKB, At_KB3),


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Get TTterms necessary for tableau building
% ??? redundant
prepare_ttTerms_KB(PrId, Align, Init_KB, PTT-HTT, AlPTT-AlHTT, Fin_KB) :-
	%prepare rule list, LLFs, and KB
	%set_rule_eff_order,
	problem_to_ttTerms(Align, PrId, PTT, HTT, AlPTT, AlHTT, KB1),
	append(Init_KB, KB1, KB2),
	sort(KB2, Fin_KB).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% get branch list for a specific entailment problem and its answer
get_branches(Ans, Align, KB, P-H, AP-AH, TTs, Brs, At_Status) :-
	( get_branches_case(Ans, Align, KB, P-H, AP-AH, TTs, Brs, Status) -> true
	% consistency checking
%	( maplist(consistency_check(KB), TTs, Checks),
%	  memberchk('Inconsistent', Checks)	->
%	  	(TTterms, Brs, Status) = (TTs, [], 'Inconsistent sentence')
	; (Brs, Status) = (['fail'], 'defected'),
	  append(AP, AH, TTs) ),
	term_to_atom(Status, At_Status).

% get branches that keep the tableau open
get_branches('unknown', Align, KB, P-H, AP-AH, _TTs, Brs, Status) :-
	% Doesn't matter which one closes, if one closes this might already mean a contrdictory knowledge
	% Entail + Contradiction = Neutral Rule is not used here
	( close_any_tableau(Align, KB, P-H, AP-AH, Status) ->	Brs = []
	; (Brs, Status) = (['unknown'], 'all open') ).%!!! or defected

%-------------------------------
get_branches_case('yes', 'align', KB, _, AP-AH, TTs, Brs, Status) :-
	append(AP, AH, TTs),
	generateTableau(KB-_, AP, AH, Brs, _, Status).

get_branches_case('yes', 'no_align', KB, P-H, _, TTs, Brs, Status) :-
	append(P, H, TTs),
	generateTableau(KB-_, P, H, Brs, _, Status).

get_branches_case('no', 'align', KB, _, AP-AH, TTs, Brs, Status) :-
	append(AP, AH, TTs),
	generateTableau(KB-_, TTs, [], Brs, _, Status).

get_branches_case('no', 'no_align', KB, P-H, _, TTs, Brs, Status) :-
	append(P, H, TTs),
	generateTableau(KB-_, TTs, [], Brs, _, Status).
%-------------------------------

% Succeeds if one of the 4 tableaux closes for ent|cont x aligned|non-alogned
close_any_tableau(Align, KB, P-H, AP-AH, Status) :-
	append(P, H, TTs),
	append(AP, AH, ATTs),
	( memberchk(Align, ['both', 'align']),
	  generateTableau(KB-_, ATTs, [], 		[], _, Status)
	; memberchk(Align, ['both', 'no_align']),
	  generateTableau(KB-_, TTs, [], 		[], _, Status)
	; memberchk(Align, ['both', 'align']),
	  generateTableau(KB-_, AP, AH, 	[], _, Status)
	; memberchk(Align, ['both', 'no_align']),
	  generateTableau(KB-_, P, H, 		[], _, Status)
	),
	!.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Find all KBs (a list of relations) that closes the given branch
% with the help of initial KB0 and closure rules
all_closing_KB(ClRules, BrNodes, KB0, L_KB) :-
	findall(Knowledge, (
		member(R, ClRules),
		closing_rule_knowledge(BrNodes, R, KB0, Knowledge)
		), KB_list),
	sort(KB_list, L_KB).

%---------------------------------------------------
% Find NewKB such that in combination with an initial KB0, it causes Branch closure
% KB0 (and NewKB) is sorted. The predicate is not deterministic!
closing_rule_knowledge(br(Nodes,_,_), Rule, KB0, NewKB) :-
	clause( r(Rule, closure, _, _, _, br(HeadNodes,_) ===> _), _Constraints ),
	findHeadNodes(Nodes, HeadNodes, _IDs),
	append(KB0, _, KB0_X),
	r(Rule, closure, _, _, KB0_X-_XP, br(HeadNodes, _) ===> _),
	uList2List(KB0_X, KB_All),
	sym_rels_to_canonical(KB_All, Cano_KB_All),
	sort(Cano_KB_All, KB_All_Sorted),
	subtract(KB_All_Sorted, KB0, NewKB).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ttTerm is of form one of the Patterns, where
% In each pattern variables stand for atoms
% e.g., a@man@run is of form A@B@C but not of A@B
pattern_filtered_nodes([], BrNodes, BrNodes) :- !.

pattern_filtered_nodes(Patterns, BrNodes, Filtered) :-
	% detecting whether BrNodes are Branch or Nodes
	( BrNodes = br(Nodes, Hist, Sig)
	->	Filtered = br(FilteredNodes, Hist, Sig)
	; 	BrNodes = Nodes,
		Filtered = FilteredNodes
	), % Filtering nodes based on patterns
	findall(NdId, (
		member(NdId, Nodes),
		ndId_of_patterns(NdId, Patterns)
		), FilteredNodes).

%-----------------------------------------
% Succeeds if LLF in node_id has a pattern from Patterns list
ndId_of_patterns(ndId(Node,_), Patterns) :-
	Node = nd(_, TT, _Args, _TF),
	member(Pat, Patterns),
	term_variables(Pat, PatVars), % get all variables of pattern
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
