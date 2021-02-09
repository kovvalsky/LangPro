%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Error, warning, info, debug,  reporting module
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:-module(reporting, [
	add_to_stream/2,
	compare_to_once_solved/1,
	report_error/2,
	throw_error/2,
	report/1,
	report/2,
	write_predictions_in_file/1,
	write_parList/1,
	print_pre_hyp/2, print_pre_hyp/1,
	par_format/2, par_format/3,
	test_true/3
	%debMode/1
]).
%==================================
:- use_module(library(ansi_term)).
:- use_module(library(term_to_json), [term_to_json/2]).
:- use_module(library(http/json), [json_write/2, json_write/3]).

:- use_module('../utils/generic_preds', [
	format_list_list/3, format_list_list/4, format_list/3
	]).
:- use_module('../llf/ttterm_to_term', [
	ttTerm_to_pretty_ttTerm/2, ndId_to_pretty/2]).

:- dynamic debMode/1.
:- dynamic sen_id/5.
:- dynamic sick_solved/2.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% repor error with formatting preceded with the ERROR keyword
report_error(Format, Values) :-
	format(atom(Message), Format, Values),
   	ansi_format([fg(red), bold], 'ERROR: ~w~n', [Message]).

throw_error(Format, Values) :-
	format(atom(Message), Format, Values),
	throw(Message).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% For testing
report(MessageList) :-
	%maplist(term_to_atom, MessageList, AtomList),
	%atomic_list_concat(AtomList, Message),
	with_output_to(atom(Message), maplist(write, MessageList)),
	writeln(Message).

report(Message, Term) :-
	\+is_list(Message),
	term_to_atom(Term, Atom),
	write(Message),
	writeln(Atom).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%          Reporting results of run
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% report parameters
write_parList(S) :-
	findall(P, debMode(P), Pars),
	format(S, '~w', [Pars]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% write prediction if a file is given
write_predictions_in_file(Results) :-
	debMode(waif(FileName)) ->
		write_predictions_in_file(FileName, Results)
	; true.

write_predictions_in_file(FileName, Results) :-
	open(FileName, write, S, [encoding(utf8), close_on_abort(true)]),
	write(S, '=== Parameters ===\n%%% '),
	write_parList(S), nl(S),
	write(S, '=== LangPro ===\n'),
	ignore(write_id_answer(S, Results)),
	close(S).

%%%%%%%%%%%%%%%%%%%%%%
% writes id answer pairs in S
% used with ignore/1 to go through all results
write_id_answer(S, Results)  :-
	member( (Id, Ans, Provers_Ans, Closed, Info), Results),
	once( 	(Provers_Ans, Std_Ans) = ('unknown', 'NEUTRAL');
			(Provers_Ans, Std_Ans) = ('yes', 'ENTAILMENT');
			(Provers_Ans, Std_Ans) = ('no', 'CONTRADICTION')
	),
	( debMode('waifx') ->
		format(atom(Text), '~t~w:~5+~t [~w],~11+~t~w,~9+~t~w,~9+ ~w~n', [Id, Ans, Std_Ans, Closed, Info])
	;   format(atom(Text), '~w\t~w~n', [Id, Std_Ans])
	),
	write(S, Text),
	fail.




%%%%%%%%%%%%%%%%%%%%%%
% print premise(s) and hypothesis (parallel aware)
print_pre_hyp(Source, PrId) :-
	findall(Sen, (
		sen_id(_, PrId, PH, _, Sent),
		atomic_list_concat([PH, Sent], ': ', Sen)
		), Sentences),
	atomic_list_concat(Sentences, '\n', Problem),
	par_format(Source, '~w~n', Problem).

print_pre_hyp(PrId) :-
	current_output(Source),
	print_pre_hyp(Source, PrId).

%%%%%%%%%%%%%%%%%%%%%%%%%
% parallel processing aware format.
% It suppresses printing is the parallel mode is on
par_format(Source, Format, List) :-
	current_output(Src),
	( debMode(parallel(_)),
	  Src = Source
	  ->
		true
	; 	format(Source, Format, List)
	).

par_format(Format, List) :-
	current_output(Source),
	par_format(Source, Format, List).


%%%%%%%%%%%%%%%%%%%%%%%%%
% compare the results to the once-solved list of problems
compare_to_once_solved(Results) :-
	debMode(once_solved:Parser),
	debMode(data:sick),
	nonvar(Parser), !,
	% all problems that were solved now but never before
	findall([ID,Gold,Pred,Cl,Info], (
		member((ID,Gold,Pred,Cl,Info), Results),
		Gold == Pred,
		\+sick_solved(ID, Parser)
	), First_time),
	length(First_time, N1),
	format('~`-t ~55|~n'),
	format('First time solved now (~w): ~n', [N1]),
	format_list_list(atom(M1), '  ~t~w:~5+~t [~w],~11+~t~w,~9+~t~w,~9+ ~w~t~12+~n', First_time),
	writeln(M1),
	% all problems that were not solved now but once before
	findall([ID,Gold,Pred,Cl,Info], (
		member((ID,Gold,Pred,Cl,Info), Results),
		Gold \= Pred,
		sick_solved(ID, Parser)
	), Not_now),
	length(Not_now, N2),
	format('~`-t ~55|~n'),
	format('Not now but once solved (~w): ~n', [N2]),
	format_list_list(atom(M2), '  ~t~w:~5+~t [~w],~11+~t~w,~9+~t~w,~9+ ~w~t~12+~n', Not_now),
	writeln(M2).

compare_to_once_solved(_).

%%%%%%%%%%%%%%%%%%%%%%%%%
% add terms to a stream that usually corresponds to an open file
add_to_stream(DataType, Data) :-
	findall(_, (
		debMode(stream(DataType, Ext, S)),
		( DataType == 'branches' ->
			add_branches_to_stream(Data, Ext, S)
		)
	), _).

add_branches_to_stream((Info, BrList), Ext, S) :-
	Info = [PrId | Mode],
	maplist([br(Nodes,Hist,Sig), json{nodes:Nodes,rules:Hist,sig:Sig}]>>true,
			BrList, L_JsonBr),
	( Ext == 'json' ->
		Dict = json{id:PrId, mode:Mode, branches:L_JsonBr},
		term_to_json(Dict, Json),
		json_write(S, Json, [width(0)])
	; Ext == 'txt' ->
		( memberchk('p', Info) -> PH = 'p'; PH = 'h' ), % FIXME: only works for single prem
		once(sen_id(_, PrId, PH, Ans, Sent)),
		format(S, 'branches: ~w~nsentence: ~w~n', [[Ans|Info], Sent]),
		findall(_, (
				member(br(NdIds,Hist,Sig), BrList),
				maplist(ndId_to_pretty, NdIds, PrettyNdIds),
				format(S, '  [~n    ~w~n', [Sig]),
				format_list(S, '    ~w~n', Hist),
				format_list(S, '    ~w~n', PrettyNdIds)
			),_)
	),
	nl(S),
	flush_output(S).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% test and raise exception
test_true(Goal, Format, Values) :-
    ( call(Goal) -> true
    ; throw_error(Format, Values) ).
