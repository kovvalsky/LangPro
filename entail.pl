


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% entailment with the first GQTT
entail_all :-
	findall( (Problem_Id, Answer), 
		sen_id(_, Problem_Id, _, Answer, _),
		ProbIds_Answers),
	remove_adjacent_duplicates(ProbIds_Answers, ProblemIds_Answers),
	retractall(debMode('proof_tree')),
	maplist(solve_entailment, ProblemIds_Answers, Results),
	draw_extended_matrix(Results).

% Consideres only problems with specific answers
entail_all(List_of_Answers) :-
	findall( (Problem_Id, Answer), 
		( sen_id(_, Problem_Id, _, Answer, _), member(Answer, List_of_Answers)  ),
		ProbIds_Answers),
	remove_adjacent_duplicates(ProbIds_Answers, ProblemIds_Answers),
	retractall(debMode('proof_tree')),
	maplist(solve_entailment, ProblemIds_Answers, Results),
	draw_extended_matrix(Results).

entail_some(List_Int) :-
	(is_list(List_Int) ->
		List = List_Int
	  ; List_Int = Inf-Sup,
		integer(Inf),
		integer(Sup),
		findall(X, between(Inf, Sup, X), List)
	),	
	findall( (Problem_Id, Answer), 
		( member(Problem_Id, List), sen_id(_, Problem_Id, _, Answer, _) ),
		ProbIds_Answers),
	remove_adjacent_duplicates(ProbIds_Answers, ProblemIds_Answers),
	retractall(debMode('proof_tree')),
	maplist(solve_entailment, ProblemIds_Answers, Results),
	draw_extended_matrix(Results).


% entailment with all GQTTs
list_entail_all :-
	findall( (Problem_Id, Answer), 
		sen_id(_, Problem_Id, _, Answer, _),
		ProbIds_Answers),
	remove_adjacent_duplicates(ProbIds_Answers, ProblemIds_Answers),
	retractall(debMode('proof_tree')),
	maplist(list_solve_entailment, ProblemIds_Answers, Results),
	%draw_matrix(Results).
	draw_extended_matrix(Results).


list_entail_some(List) :-
	findall( (Problem_Id, Answer), 
		( member(Problem_Id, List), sen_id(_, Problem_Id, _, Answer, _) ),
		ProbIds_Answers),
	remove_adjacent_duplicates(ProbIds_Answers, ProblemIds_Answers),
	retractall(debMode('proof_tree')),
	maplist(list_solve_entailment, ProblemIds_Answers, Results),
	draw_matrix(Results).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Creates result pairs
list_solve_entailment( (Id, Answer), (Id, Ans, Closed, Status) ) :-
	(Answer = 'undef' -> 
		Ans = 'unknown'
	  ; Ans = Answer
	),
	list_entail(Id, Ans, Closed, Status),
	format('~t~w:~4+~t~w,~9+~t~w,~8+ ~w~t~12+~n', [Id, Ans, Closed, Status]).
/*	list_entail(Id) ->
		( Answer == yes ->  % can deal with answers "yes" and rest
			write(Id), write('-yes,'), writeln(' pass'), Result = (yes, true);
		  	write(Id), write('-no, '), writeln(' fail'), Result = (no, true) );
		( Answer == yes -> 
			write(Id), write('-yes,'), writeln(' fail'), Result = (yes, false);
			write(Id), write('-no, '), writeln(' pass'), Result = (no, false) ).
*/

solve_entailment( (Id, Answer), (Id, Ans, Provers_Ans, Closed, Status) ) :-
	( Answer = 'undef' -> 
		Ans = 'unknown'
	  ; Ans = Answer
	),
	( debMode('2class') ->
		entail_2(Id, Ans, Provers_Ans, Closed, Status)
	  ;	entail(Id, Ans, Provers_Ans, Closed, Status)
	),
	( debMode('prprb') ->  findall(Sen, sen_id(_,Id,_,_,Sen), Sentences), maplist(writeln, Sentences); true ),
	format('~t~w:~5+~t [~w],~11+~t~w,~9+~t~w,~9+ ~w~t~12+~n', [Id, Ans, Provers_Ans, Closed, Status]).



%%%%%%%%%%%%%%%%%%%%%%
% writes id answer pairs in S
write_id_answer(S, Results)  :-
	member( (Id, _, Provers_Ans, _, _), Results),
	once( 	(Provers_Ans, Ans) = ('unknown', 'NEUTRAL'); 
			(Provers_Ans, Ans) = ('yes', 'ENTAILMENT');
			(Provers_Ans, Ans) = ('no', 'CONTRADICTION')  
	),
	atomic_list_concat([Id, '\t', Ans, '\n'], Text),
	write(S, Text),
	fail.
	
	% Numbers for matrix


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Draws confusion matrix
draw_matrix(Results) :-
	findall(_, member((yes, true), Results), Yes_True),
	findall(_, member((yes, false),Results), Yes_False), 
	findall(_, member((no, true), 	Results), No_True),
	findall(_, member((no, false), Results), No_False),
	length(Yes_True, YesTrue),
	length(Yes_False, YesFalse),
	length(No_True, NoTrue),
	length(No_False, NoFalse),
	length(Results, Total),
	format('~45t ~25|~n'),
	format('      ~t True~12|~t Fasle~8+~n'),
	format(' Yes: ~t ~2f~12|~t~2f~8+~n', [YesTrue/Total, YesFalse/Total]),
	format('      ~t ~w~12|~t~w~8+~n', [YesTrue, YesFalse]),
	format('~45t ~25|~n'),
	format(' No : ~t ~2f~12|~t~2f~8+~n', [NoTrue/Total, NoFalse/Total]),
	format('      ~t ~w~12|~t~w~8+~n', [NoTrue, NoFalse]),
	format('~45t ~25|~n').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Draws extended tableau for evaluation
draw_extended_matrix(Results) :-
	( debMode('2class') ->
		draw_extended_matrix_2(Results)
	  ; draw_extended_matrix_3(Results)
	).


draw_extended_matrix_3(Results) :-
	( debMode(waif(FileName)) -> 
		open(FileName, write, S, [encoding(utf8), close_on_abort(true)]),
		write(S, '=== LangPro ===\n'),
		ignore(write_id_answer(S, Results)),
		close(S)
	; true
	),
	% Numbers for matrix
	findall( _,	member((_, 'yes',	'yes', 		'closed',	'Terminated'), 	Results),	Y_Y), 	length(Y_Y, YY),
	findall( _,	member((_, 'yes',	'no', 		'closed', 	'Terminated'), 	Results),	Y_N), 	length(Y_N, YN),
	findall( _,	member((_, 'yes',	'unknown', 	'open', 	_),				Results),	Y_U), 	length(Y_U, YU),
	findall( _,	member((_, 'yes',	'unknown', 	'open', 	'Limited'),		Results),	Y_U_L), length(Y_U_L, YUL),
	findall( _,	member((_, 'yes',	'unknown', 	'NA', 		'Defected'), 	Results),	Y_D), 	length(Y_D, YD),

	findall( _,	member((_, 'no',	'yes', 		'closed',	'Terminated'), 	Results),	N_Y), 	length(N_Y, NY),
	findall( _,	member((_, 'no',	'no', 		'closed', 	'Terminated'), 	Results),	N_N), 	length(N_N, NN),
	findall( _,	member((_, 'no',	'unknown', 	'open', 	_),				Results),	N_U), 	length(N_U, NU),
	findall( _,	member((_, 'no',	'unknown', 	'open', 	'Limited'),		Results),	N_U_L), length(N_U_L, NUL),
	findall( _,	member((_, 'no',	'unknown', 	'NA', 		'Defected'), 	Results),	N_D), 	length(N_D, ND),

	findall( _,	member((_, 'unknown',	'yes', 		'closed',	'Terminated'), 	Results),	U_Y), 	length(U_Y, UY),
	findall( _,	member((_, 'unknown',	'no', 		'closed', 	'Terminated'), 	Results),	U_N), 	length(U_N, UN),
	findall( _,	member((_, 'unknown',	'unknown', 	'open', 	_),				Results),	U_U), 	length(U_U, UU),
	findall( _,	member((_, 'unknown',	'unknown', 	'open', 	'Limited'),		Results),	U_U_L), length(U_U_L, UUL),
	findall( _,	member((_, 'unknown',	'unknown', 	'NA',		'Defected'), 	Results),	U_D), 	length(U_D, UD),
	% Calculating useful numbers
	sum_list([YY, NN], 					YY_NN),
	sum_list([YY_NN, YN, NY, UY, UN], 	YNU_YN),
	( YNU_YN \= 0 ->  	Prec = YY_NN / YNU_YN; 	Prec = 2 ),

	sum_list([YY_NN, YN, NY, YU, NU], 	YN_YNU),
	sum_list([YN_YNU, YD, ND],			YN_YNUD),
	( YN_YNUD \= 0 ->  	Rec = YY_NN / YN_YNUD; 		Rec = 2 ),   
	( YN_YNU \= 0 ->  	TrRec = YY_NN / YN_YNU; 	TrRec = 2 ),   

	sum_list([YY_NN, UU], 			YY_NN_UU),
	sum_list([YN_YNU, UY, UN, UU],	YNU_YNU),	
	sum_list([YNU_YNU, YD, ND, UD],	YNU_YNUD),
	sum_list([YY_NN_UU, UD],		YY_NN_UU_UD),
	( YNU_YNUD \= 0 ->  Acc = YY_NN_UU_UD / YNU_YNUD; 	Acc = 2 ),   
	( YNU_YNU \= 0 ->  	TrAcc = YY_NN_UU / YNU_YNU; 	TrAcc = 2 ), 
	% checking on correctness
	length(Results, Total),
	(YNU_YNUD is Total -> 	true; 	report(['Warnning: Matrix calculation']) ),
	% printing
	( member(('no_unk',	_, _), Results) -> % needs attantion
		% 2 way classification
		report(['Binary classification output needs attention!'])
		/*format('~`-t ~50|~n'),
		format('      ~t Closed~18|~t Open~13+~t Defected~12+~n'),
		format(' Yes: ~t ~w~12+~t(~w)~6+~t~w~7+~t(~w)~6+~t~w~12+~n', [Cl_Yes_, Cl_Yes_Lim_, Op_Yes_, Op_Yes_Lim_, Def_Yes_]),
		format('~`-t ~50|~n'),
		format(' No_Unk: ~t ~w~12+~t(~w)~6+~t~w~7+~t(~w)~6+~t~w~12+~n', [Cl_NoUnk_, Cl_NoUnk_Lim_, Op_NoUnk_, Op_NoUnk_Lim_, Def_NoUnk_]),
		format('~`-t ~50|~n')*/
	  ;	% 3 way classification
		format('~`-t ~55|~n'),
		format(' Gold\\Prover ~t YES~22+ ~t NO~9+ ~t UNK  ~12+ ~t DEF~8+~n'),
		format('~`-t ~55|~n'),
		format(' ENTAILMENT: ~t ~w ~22+ ~t ~w ~9+ ~t ~w (~w)~12+ ~t ~w ~8+~n', [YY, YN, YU, YUL, YD]),
		format('~`-t ~55|~n'),
		format(' CONTRADICTION: ~t ~w ~22+ ~t ~w ~9+ ~t ~w (~w)~12+ ~t ~w ~8+~n', [NY, NN, NU, NUL, ND]),
		format('~`-t ~55|~n'),
		format(' NEUTRAL: ~t ~w ~22+ ~t ~w ~9+ ~t ~w (~w)~12+ ~t ~w ~8+~n', [UY, UN, UU, UUL, UD]),
		format('~`-t ~55|~n'),
		format('Total #problems:  ~d~n', 	[Total]),
		format('Accuracy (pure):  ~5f    (~5f)~n', 	[Acc, TrAcc]),
		format('Precision:        ~5f~n', 		  	[Prec]),
		format('Recall (pure):    ~5f    (~5f)~n', 	[Rec, TrRec])
	).



draw_extended_matrix_2(Results) :-
	( debMode(waif(FileName)) -> 
		open(FileName, write, S, [encoding(utf8), close_on_abort(true)]),
		write(S, '=== LangPro ===\n'),
		ignore(write_id_answer(S, Results)),
		close(S)
	; true
	),
	% Numbers for matrix
	findall( _,	member((_, 'yes',	'yes', 		'closed',	'Terminated'), 	Results),	Y_Y), 	length(Y_Y, YY),
	findall( _,	member((_, 'yes',	'no_unk', 	'open', 	_),				Results),	Y_U), 	length(Y_U, YU),
	findall( _,	member((_, 'yes',	'no_unk', 	'open', 	'Limited'),		Results),	Y_U_L), length(Y_U_L, YUL),
	findall( _,	member((_, 'yes',	'no_unk', 	'NA', 		'Defected'), 	Results),	Y_D), 	length(Y_D, YD),

	findall( _,	member((_, 'no_unk',	'yes', 		'closed',	'Terminated'), 	Results),	U_Y), 	length(U_Y, UY),
	findall( _,	member((_, 'no_unk',	'no_unk', 	'open', 	_),				Results),	U_U), 	length(U_U, UU),
	findall( _,	member((_, 'no_unk',	'no_unk', 	'open', 	'Limited'),		Results),	U_U_L), length(U_U_L, UUL),
	findall( _,	member((_, 'no_unk',	'no_unk', 	'NA',		'Defected'), 	Results),	U_D), 	length(U_D, UD),
	% Calculating useful numbers
	sum_list([YY, UY], 	YUxY),
	( YUxY \= 0 ->  	Prec = YY / YUxY; 	Prec = 2 ),

	sum_list([YY, YU], 	YxYU),
	sum_list([YxYU, YD], YxYUD),
	( YxYUD \= 0 ->  	Rec = YY / YxYUD; 	Rec = 2 ),   
	( YxYU \= 0  ->  	TrRec = YY / YxYU; 	TrRec = 2 ),   

	sum_list([YY, UU], YY_UU),
	sum_list([YY_UU, UY, YU],	YUxYU),	
	sum_list([YUxYU, YD, UD],	YUxYUD),
	sum_list([YY_UU, UD],		YY_UU_UD),
	( YUxYUD \= 0 ->  Acc = YY_UU_UD / YUxYUD; 	Acc = 2 ),   
	( YUxYU \= 0 ->  	TrAcc = YY_UU / YUxYU; 	TrAcc = 2 ), 
	% checking on correctness
	length(Results, Total),
	(YUxYUD is Total -> 	true; 	report(['Warnning: Matrix calculation']) ),
	% printing
	( %2 way classification
		format('~`-t ~55|~n'),
		format(' Gold\\Prover ~t YES~22+ ~t CONT_UNK~12+ ~t DEF~8+~n'),
		format('~`-t ~55|~n'),
		format(' ENTAILMENT: ~t ~w ~22+ ~t ~w (~w)~12+ ~t ~w ~8+~n', [YY, YU, YUL, YD]),
		format('~`-t ~55|~n'),
		format(' CONT_UNK: ~t ~w ~22+ ~t ~w (~w)~12+ ~t ~w ~8+~n', [UY, UU, UUL, UD]),
		format('~`-t ~55|~n'),
		format('Total #problems:  ~d~n', 	[Total]),
		format('Accuracy (pure):  ~5f    (~5f)~n', 	[Acc, TrAcc]),
		format('Precision:        ~5f~n', 		  	[Prec]),
		format('Recall (pure):    ~5f    (~5f)~n', 	[Rec, TrRec])
	).



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
check_problem(Prem_TTterms, Hypo_TTterms, 'yes', Provers_Ans, Closed, Status, Tree) :-
	!,
	( generateTableau(Prem_TTterms, Hypo_TTterms, BrList, Tree, Steps) ->
		( integer(Steps) ->
			Status = 'Terminated'
		;	Status = 'Limited'), 
		( BrList = [] ->
			Closed = 'closed', Provers_Ans = 'yes'
		;	Closed = 'open',   Provers_Ans = 'unknown')
	; 	Closed = 'NA',
		Provers_Ans = 'unknown',
		Status = 'Defected'
	).

check_problem(Prem_TTterms, Hypo_TTterms, 'no_unk', Provers_Ans, Closed, Status, Tree) :- %Wrong
	!,
	check_problem(Prem_TTterms, Hypo_TTterms, 'yes', Provers_Ans, Closed, Status, Tree).
	
	

check_problem(Prem_TTterms, Hypo_TTterms, 'no', Provers_Ans, Closed, Status, Tree) :-
	!,
	append(Prem_TTterms, Hypo_TTterms, TTterms),
	( generateTableau(TTterms, [], BrList, Tree, Steps) ->
		( integer(Steps) ->
			Status = 'Terminated'
		;	Status = 'Limited'), 
		( BrList = [] ->
			Closed = 'closed', Provers_Ans = 'no'
		;	Closed = 'open',   Provers_Ans = 'unknown')
	; 	Closed = 'NA',
		Provers_Ans = 'unknown',
		Status = 'Defected'
	).

check_problem(Prem_TTterms, Hypo_TTterms, 'unknown', Provers_Ans, Closed, Status, _) :-
	!,
	check_problem(Prem_TTterms, Hypo_TTterms, 'yes', Provers_Ans_yes, Closed1, Status1, _Tree1),
	check_problem(Prem_TTterms, Hypo_TTterms, 'no', Provers_Ans_no, Closed2, Status2, _Tree2),
	( Closed1 == 'closed' ->
		(Provers_Ans, Closed, Status) = (Provers_Ans_yes, 'closed', 'Terminated')
	; Closed2 == 'closed' ->
		(Provers_Ans, Closed, Status) = (Provers_Ans_no, 'closed', 'Terminated')
	; (Closed1 == 'NA'; Closed2 == 'NA') ->
		Closed = 'NA', Status = 'Defected', Provers_Ans = 'unknown'
	; (Status1 = 'Limited'; Status2 = 'Limited') ->
		Status = 'Limited', Closed = 'open', Provers_Ans = 'unknown'
	; Status = 'Terminated', Closed = 'open', Provers_Ans = 'unknown' 		
	).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% solves a problem vs check
solve_problem(Prem_TTterms, Hypo_TTterms, Prover_Ans, Closed, Status) :-
	check_problem(Prem_TTterms, Hypo_TTterms, 'yes', _, Closed_yes, Status_yes, _),
	check_problem(Prem_TTterms, Hypo_TTterms, 'no', _,  Closed_no, Status_no, _),
	( (Closed_yes, Closed_no) == ('closed', 'closed') ->
		report(['Warning: CONTRADICTION and ENTAILMENT at the same time: but ENTAILMENT']),
		(Prover_Ans, Closed, Status)  = ('yes', 'closed', 'Terminated')  %!!!
	; (Closed_yes, Closed_no) == ('closed', 'open') ->
		(Prover_Ans, Closed, Status)  = ('yes', Closed_yes, Status_yes)  
	; (Closed_yes, Closed_no) == ('open', 'closed') ->
		(Prover_Ans, Closed, Status)  = ('no', Closed_no, Status_no)  
	; (Closed_yes, Closed_no) == ('open', 'open') ->
		( (Status_yes == 'Limited'; Status_no = 'Limited') ->	Status = 'Limited';   Status = 'Terminated' ), 
		(Prover_Ans, Closed)  = ('unknown', 'open')  
   	; (Closed_yes == 'NA'; Closed_no == 'NA') ->
		(Prover_Ans, Closed, Status)  = ('unknown', 'NA', 'Defected')
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
%/*
% solves problems - doesnt knows the answer beforehand	  
entail(Problem_Id, _Answer, Provers_Answer, Closed, FinalStatus) :-
	findall(_X, sen_id(_, Problem_Id, _, _, _), Prem_Hyp), % finds the length of the problem
	%problem_id_TTterms(Problem_Id, Prem_TTs, Hypo_TTs), Align_Prem_TTs = Prem_TTs, Align_Hypo_TTs = Hypo_TTs,
	problem_to_ttTerms('align', Problem_Id, Prem_TTs, Hypo_TTs, Align_Prem_TTs, Align_Hypo_TTs),
	solve_problem(Prem_TTs, Hypo_TTs, NoA_Prov_Ans, NoA_Closed, NoA_Status), 
	solve_problem(Align_Prem_TTs, Align_Hypo_TTs, Align_Prov_Ans, Align_Closed, Align_Status),
	( Align_Closed \== 'closed', NoA_Closed \== 'closed', \+append(Prem_TTs, Hypo_TTs, Prem_Hyp) -> % if an item in the problem is defected
		(Provers_Answer, Closed, FinalStatus) = ('unknown', 'NA', 'Defected')
	; Align_Closed == 'closed' ->
		(Provers_Answer, Closed, FinalStatus) =  (Align_Prov_Ans, Align_Closed, Align_Status)
    ; (Provers_Answer, Closed, FinalStatus)   =  (NoA_Prov_Ans, NoA_Closed, NoA_Status)
	),	!.
%*/

% entailment for binary classification
entail_2(Problem_Id, _Answer, Provers_Answer, Closed, FinalStatus) :-
	findall(_X, sen_id(_, Problem_Id, _, _, _), Prem_Hyp), % finds the length of the problem
	%problem_id_TTterms(Problem_Id, Prem_TTs, Hypo_TTs), Align_Prem_TTs = Prem_TTs, Align_Hypo_TTs = Hypo_TTs,
	problem_to_ttTerms('align', Problem_Id, Prem_TTs, Hypo_TTs, Align_Prem_TTs, Align_Hypo_TTs),
	% check on yes entailment both non-aligned and aligned TTs
	check_problem(Prem_TTs, Hypo_TTs, 'yes', _, NoA_Closed, NoA_Status, _),
	check_problem(Align_Prem_TTs, Align_Hypo_TTs, 'yes', _, Al_Closed, Al_Status, _),
	% compute final answer
	( Al_Closed \== 'closed', NoA_Closed \== 'closed', \+append(Prem_TTs, Hypo_TTs, Prem_Hyp) -> % if an item in the problem is defected
		(Provers_Answer, Closed, FinalStatus) = ('no_unk', 'NA', 'Defected')
	; Al_Closed == 'closed' ->
		(Provers_Answer, Closed, FinalStatus) =  ('yes', Al_Closed, Al_Status)
    ; NoA_Closed == 'closed' ->
		(Provers_Answer, Closed, FinalStatus)   =  ('yes', NoA_Closed, NoA_Status)
	; (Provers_Answer, Closed, FinalStatus)   =  ('no_unk', NoA_Closed, NoA_Status)
	),	!.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% checks on entailment a problem with its Id
% uses several readings
list_entail(Problem_Id, Answer, Closed, FinalStatus) :-
	findall(_X, sen_id(_, Problem_Id, _, _, _), Prem_Hyp), % finds the length of the problem
	%problem_id_list_TTterms(Problem_Id, List_Prem_TTterms, List_Hypo_TTterms),
	problem_to_list_ttTerms('align', Problem_Id, List_Prem_TTterms, List_Hypo_TTterms, List_Align_Prem_TTterms, List_Align_Hypo_TTterms),
	% once(list_reason(List_of_Lists)).
	%( append(List_Prem_TTterms, List_Hypo_TTterms, Prem_Hyp) ->
	( maplist(member, Prem_TTterms, List_Prem_TTterms),
      maplist(member, Hypo_TTterms, List_Hypo_TTterms),
	  %once(append(TextList, [Hypo], TTterms)),
	  check_problem(Prem_TTterms, Hypo_TTterms, Answer, _, 'closed', NoA_Status, _) ->
		  NoA_Closed = 'closed'
		  %Status = Status1
	    ; NoA_Closed = 'open',
		  once(  (maplist(member, Prem_TTterms, List_Prem_TTterms),
	  	          maplist(member, Hypo_TTterms, List_Hypo_TTterms))  ),
		  check_problem(Prem_TTterms, Hypo_TTterms, Answer, _, _Open1, NoA_Status, _)
	),
	( maplist(member, Align_Prem_TTterms, List_Align_Prem_TTterms),
      maplist(member, Align_Hypo_TTterms, List_Align_Hypo_TTterms),
	  %once(append(TextList, [Hypo], TTterms)),
	  check_problem(Align_Prem_TTterms, Align_Hypo_TTterms, Answer, _, 'closed', Align_Status, _) ->
		  Align_Closed = 'closed'
		  %Status = Status1
	    ; Align_Closed = 'open',
		  once(  (maplist(member, Align_Prem_TTterms, List_Align_Prem_TTterms),
	  	          maplist(member, Align_Hypo_TTterms, List_Align_Hypo_TTterms))  ),
		  check_problem(Align_Prem_TTterms, Align_Hypo_TTterms, Answer, _, _Open2, Align_Status, _)
	),
	( Align_Closed \= 'closed', 
	  NoA_Closed \= 'closed', 
	  \+append(List_Prem_TTterms, List_Hypo_TTterms, Prem_Hyp) -> % if an item in the problem is defected
		FinalStatus = 'Defected'
	  ; ( Align_Closed = 'closed' ->
		    FinalStatus = Align_Status, Closed = Align_Closed
          ; FinalStatus = NoA_Status,   Closed = NoA_Closed 
		)
	),
	!.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% checks on GUI entailment a problem with its Id
% uses a single reading
gentail(Problem_Id) :-
	gentail('noalign', Problem_Id).

gentail(Align, Problem_Id) :-
	once(sen_id(_, Problem_Id, _, Answer, _)),
	%problem_id_TTterms(Problem_Id, Prem_TTterms, Hypo_TTterms),
	( Align == 'align' ->
		problem_to_ttTerms(Align, Problem_Id, _, _, Prem_TTterms, Hypo_TTterms)
	  ; problem_to_ttTerms('no_align', Problem_Id, Prem_TTterms, Hypo_TTterms, _, _)
	),
	findall(ccg(Id, CCGTree), 
			( sen_id(Id, Problem_Id, _, _, _),
			  ccg(Id, CCGTree) ), 
			CCG_IDs
	),
	ccgs_to_llfs_latex(CCG_IDs),
	( Prem_TTterms = [], Hypo_TTterms = [] ->
		writeln('Problem with this id plausibly does not exist!')
	; Prem_TTterms = [] ->
		writeln('No premises found for this problem!')
	; Hypo_TTterms = [] ->
		writeln('No hypothesis found for this problem!')
	;	% Reason! problem is ok
	  Answer = 'no' ->
		append(Prem_TTterms, Hypo_TTterms, TTterms),		
		greason(TTterms, [], Problem_Id)
	; Answer = 'yes' ->
		greason(Prem_TTterms, Hypo_TTterms, Problem_Id)
	; greason(Prem_TTterms, Hypo_TTterms, Problem_Id) ->
		true
	; append(Prem_TTterms, Hypo_TTterms, TTterms),
	  greason(TTterms, [], Problem_Id)
	).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% doesnt take into account answer of the problem
gentail_no_answer(Align, Problem_Id) :-
	once(sen_id(_, Problem_Id, _, Answer, _)),
	%problem_id_TTterms(Problem_Id, Prem_TTterms, Hypo_TTterms),
	( Align == 'align' ->
		problem_to_ttTerms(Align, Problem_Id, _, _, Prem_TTterms, Hypo_TTterms)
	  ; problem_to_ttTerms('no_align', Problem_Id, Prem_TTterms, Hypo_TTterms, _, _)
	),
	findall(ccg(Id, CCGTree), 
			( sen_id(Id, Problem_Id, _, _, _),
			  ccg(Id, CCGTree) ), 
			CCG_IDs
	),
	ccgs_to_llfs_latex(CCG_IDs),
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
		ignore(greason(Prem_TTterms, Hypo_TTterms, Problem_Id)),		
		greason(TTterms, [], Problem_Id)
	; Answer = 'yes' ->
		ignore(greason(TTterms, [], Problem_Id)),
		greason(Prem_TTterms, Hypo_TTterms, Problem_Id)
	; greason(Prem_TTterms, Hypo_TTterms, Problem_Id) ->
		true
	; %append(Prem_TTterms, Hypo_TTterms, TTterms),
	  greason(TTterms, [], Problem_Id)
	).
	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% checks on GUI entailment a problem with its Id
% uses several readings
list_gentail(Problem_Id) :-
	list_gentail('no_align', Problem_Id).

list_gentail(Align, Problem_Id) :-
	once(sen_id(_, Problem_Id, _, Answer, _)),	
	%problem_id_list_TTterms(Problem_Id, List_Prem_TTterms, List_Hypo_TTterms),
	( Align == 'align' ->
		problem_to_list_ttTerms(Align, Problem_Id, _, _, List_Prem_TTterms, List_Hypo_TTterms)
	  ; problem_to_list_ttTerms('no_align', Problem_Id, List_Prem_TTterms, List_Hypo_TTterms, _, _)
	),
	%once(list_reason(List_of_Lists)).
	maplist(member, Prem_TTterms, List_Prem_TTterms),
	maplist(member, Hypo_TTterms, List_Hypo_TTterms),
	%once(append(TextList, [Hypo], TTterms)),
	( Answer = 'no' ->
		append(Prem_TTterms, Hypo_TTterms, New_Prem_TTterms),
		New_Hypo_TTterms = []
	  ; New_Prem_TTterms = Prem_TTterms,
		New_Hypo_TTterms = Hypo_TTterms  
	),
	greason(New_Prem_TTterms, New_Hypo_TTterms, Problem_Id).


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
% 
problem_to_ttTerms(Align, Prob_Id, Prems, Hypos, Align_Prems, Align_Hypos) :-
	findall(Sen_Id, sen_id(Sen_Id, Prob_Id, 'p', _, _), Prem_Sen_Ids),
	findall(Sen_Id, sen_id(Sen_Id, Prob_Id, 'h', _, _), Hypo_Sen_Ids),
	findall(CCGTree,	( member(Id, Prem_Sen_Ids), ccg(Id, CCGTree) ),		PremCCGTrees),
	findall(CCGTree, 	( member(Id, Hypo_Sen_Ids), ccg(Id, CCGTree) ),		HypoCCGTrees),
	maplist(ccgTree_to_correct_ccgTerm, PremCCGTrees, PremCCGTerms),
	maplist(ccgTree_to_correct_ccgTerm, HypoCCGTrees, HypoCCGTerms),
	% extracting WN_relations for aligning
	append(PremCCGTerms, HypoCCGTerms, AllCCGTerms),
	extract_lex_NNPs_ttTerms(AllCCGTerms, Lexicon, _Names), 
	( debMode('lex') -> report([Lexicon]); true),
	( debMode('subWN') -> subWN_from_wn(Lexicon); rels_from_wn(Lexicon) ), 
	( debMode('no_gq_llfs') ->
		(Prems, Hypos) = (PremCCGTerms, HypoCCGTerms)
	  ; findall(Y, 	(member(X, PremCCGTerms), once_gen_quant_tt(X, Y)), 	Prems),
	    findall(Y, 	(member(X, HypoCCGTerms), once_gen_quant_tt(X, Y)), 	Hypos)
	),
	% if align flag is on
	( Align == 'align' ->
		append(PremCCGTerms, HypoCCGTerms, CCGTerms),
		align_ttTerms(CCGTerms, Align_CCGTerms, _),
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
problem_to_list_ttTerms(Align, Prob_Id, List_Prems_R, List_Hypos_R, List_Align_Prems_R, List_Align_Hypos_R) :-
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
		align_ttTerms(CCGTerms, Align_CCGTerms, _),
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



