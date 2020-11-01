%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- module('conf_matrix',
	[
		draw_matrix/1,
		draw_extended_matrix/2
	]).

:- use_module('../printer/reporting', [
	compare_to_once_solved/1, report/1, write_predictions_in_file/1
	]).

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
draw_extended_matrix(Results, [Total,Acc,Prec,Rec]) :-
	( debMode('2class') ->
		draw_extended_matrix_2(Results, 'nil')
	  ; draw_extended_matrix_3(Results, [Total,Acc,Prec,Rec])
	).


draw_extended_matrix_3(Results, [Total,Acc,Prec,Rec]) :-
	write_predictions_in_file(Results),
	compare_to_once_solved(Results),
	% rule application count
	( debMode('shallow') -> true;
	  findall( Step,	member((_, _, _, 'closed', (_Ter, Step)), Results),  Steps ),
	  sum_list(Steps, TotalSteps),
	  length(Steps, NumClosed),
	  ( NumClosed \=0 -> AvStep = TotalSteps / NumClosed; AvStep = 0 )
	),
	% Numbers for matrix
	findall( _,	member((_, 'yes',	'yes', 		'closed',	_), 			Results),	Y_Y), 	length(Y_Y, YY),
	findall( _,	member((_, 'yes',	'no', 		'closed', 	_), 			Results),	Y_N), 	length(Y_N, YN),
	findall( _,	member((_, 'yes',	'unknown', 	'open', 	_),				Results),	Y_U), 	length(Y_U, YU),
	findall( _,	member((_, 'yes',	'unknown', 	'open', 	('Lim',_)),		Results),	Y_U_L), length(Y_U_L, YUL),
	findall( _,	member((_, 'yes',	'unknown', 	'NA', 		'Defected'), 	Results),	Y_D), 	length(Y_D, YD),

	findall( _,	member((_, 'no',	'yes', 		'closed',	_), 			Results),	N_Y), 	length(N_Y, NY),
	findall( _,	member((_, 'no',	'no', 		'closed', 	_), 			Results),	N_N), 	length(N_N, NN),
	findall( _,	member((_, 'no',	'unknown', 	'open', 	_),				Results),	N_U), 	length(N_U, NU),
	findall( _,	member((_, 'no',	'unknown', 	'open', 	('Lim',_)),		Results),	N_U_L), length(N_U_L, NUL),
	findall( _,	member((_, 'no',	'unknown', 	'NA', 		'Defected'), 	Results),	N_D), 	length(N_D, ND),

	findall( _,	member((_, 'unknown',	'yes', 		'closed',	_), 		Results),	U_Y), 	length(U_Y, UY),
	findall( _,	member((_, 'unknown',	'no', 		'closed', 	_), 		Results),	U_N), 	length(U_N, UN),
	findall( _,	member((_, 'unknown',	'unknown', 	'open', 	_),			Results),	U_U), 	length(U_U, UU),
	findall( _,	member((_, 'unknown',	'unknown', 	'open', 	('Lim',_)),	Results),	U_U_L), length(U_U_L, UUL),
	findall( _,	member((_, 'unknown',	'unknown', 	'NA',		'Defected'),Results),	U_D), 	length(U_D, UD),
	% Calculating useful numbers
	sum_list([YY, NN], 					YY_NN),
	sum_list([YY_NN, YN, NY, UY, UN], 	YNU_YN),
	( YNU_YN \= 0 ->  	Prec = YY_NN / YNU_YN; 	Prec = 0 ),

	sum_list([YY_NN, YN, NY, YU, NU], 	YN_YNU),
	sum_list([YN_YNU, YD, ND],			YN_YNUD),
	( YN_YNUD \= 0 ->  	Rec = YY_NN / YN_YNUD; 		Rec = 0 ),
	( YN_YNU \= 0 ->  	TrRec = YY_NN / YN_YNU; 	TrRec = 0 ),

	sum_list([YY_NN, UU], 			YY_NN_UU),
	sum_list([YN_YNU, UY, UN, UU],	YNU_YNU),
	sum_list([YNU_YNU, YD, ND, UD],	YNU_YNUD),
	sum_list([YY_NN_UU, UD],		YY_NN_UU_UD),
	( YNU_YNUD \= 0 ->  Acc = YY_NN_UU_UD / YNU_YNUD; 	Acc = 0 ),
	( YNU_YNU \= 0 ->  	TrAcc = YY_NN_UU / YNU_YNU; 	TrAcc = 0 ),
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
	),
	( debMode('shallow') -> true;
	  write('------------ STATS -------------\n'),
	  format('~w: ~30+ ~d~n', 	['Total #clTabperPrb', NumClosed]),
	  format('~w: ~30+ ~d~n', 	['Total #ruleApps for clTab', TotalSteps]),
	  format('~w: ~30+ ~5f~n', 	['Average #ruleApps for clTab', AvStep])
	).



draw_extended_matrix_2(Results, 'nil') :-
	write_predictions_in_file(Results),
	compare_to_once_solved(Results),
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
	( YUxY \= 0 ->  	Prec = YY / YUxY; 	Prec = 0 ),

	sum_list([YY, YU], 	YxYU),
	sum_list([YxYU, YD], YxYUD),
	( YxYUD \= 0 ->  	Rec = YY / YxYUD; 	Rec = 0 ),
	( YxYU \= 0  ->  	TrRec = YY / YxYU; 	TrRec = 0 ),

	sum_list([YY, UU], YY_UU),
	sum_list([YY_UU, UY, YU],	YUxYU),
	sum_list([YUxYU, YD, UD],	YUxYUD),
	sum_list([YY_UU, UD],		YY_UU_UD),
	( YUxYUD \= 0 ->  Acc = YY_UU_UD / YUxYUD; 	Acc = 0 ),
	( YUxYU \= 0 ->  	TrAcc = YY_UU / YUxYU; 	TrAcc = 0 ),
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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% print prediction results and details in one line
print_result((Id, Ans, Provers_Ans, Closed, Status, XP)) :-
	format('~t~w:~5+~t [~w],~11+~t~w,~9+~t~w,~9+ ~w~t~12+ XP: ~w~n', [Id, Ans, Provers_Ans, Closed, Status, XP]).
