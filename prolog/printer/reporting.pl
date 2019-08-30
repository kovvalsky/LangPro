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
	report/2	
]).
%==================================
:- use_module(library(ansi_term)).
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
	   	 
	
