%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Error, warning, info, debug,  reporting module
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:-module(reporting, [
	report_error/2,
	throw_error/2,
	report/1,
	report/2,
	write_predictions_in_file/1
	%debMode/1
]).
%==================================
:- use_module(library(ansi_term)).
%:- dynamic debMode/1.
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
	member( (Id, _, Provers_Ans, _, _), Results),
	once( 	(Provers_Ans, Ans) = ('unknown', 'NEUTRAL');
			(Provers_Ans, Ans) = ('yes', 'ENTAILMENT');
			(Provers_Ans, Ans) = ('no', 'CONTRADICTION')
	),
	atomic_list_concat([Id, '\t', Ans, '\n'], Text),
	write(S, Text),
	fail.
