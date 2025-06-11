%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Contains predicates used for online version
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module('../xml/xml_output', [write_parsed_problem_as_xml/3, write_xml_proof_tree/3]).
:- use_module('../json/json_output', [write_parsed_problem_as_json/3, write_json_proof_tree/3]).
:- use_module('../utils/user_preds', [print_prob/1]).
:- use_module('../printer/reporting', [report/1]).
:- use_module('../rules/rule_hierarchy', [set_rule_eff_order/0]).
:- use_module(library(term_to_json), [term_to_json/2]).
:- use_module(library(http/json), [json_write/2, json_write/3]).

:- op(601, xfx, (/)).
:- op(601, xfx, (\)).

:- dynamic sen_id/5.
:- dynamic ccg/2.

online_demo(ID) :-
	\+sen_id(_,ID,_,_,_),
	!,
	report(['There is no problem with ID=', ID, ' in the selected data set']).


online_demo(ID) :-
	online_demo(ID, 'xml').

online_demo(ID, Format) :-
	%report(['Entering online_demo/1\n']),
	%entail(1, _Answer, Provers_Answer, Closed, FinalStatus),
	%print_problem(ID),
	current_output(S),
	problem_to_ttTerms('align', ID, Prems, Hypos, Align_Prems, Align_Hypos, KB),
	set_rule_eff_order,
	check_problem(KB-_, Align_Prems, Align_Hypos, 'yes', _, Al_Cl_yes, Al_St_yes, _, Al_Tr_yes),
	( Al_St_yes \== 'Defected' ->
		check_problem(KB-_, Align_Prems, Align_Hypos, 'no', _,  Al_Cl_no, Al_St_no, _, Al_Tr_no),
		check_problem(KB-_, Prems, Hypos, 'yes', _, Cl_yes, St_yes, _, Tr_yes),
		check_problem(KB-_, Prems, Hypos, 'no', _,  Cl_no, St_no, _, Tr_no),
		( Al_Cl_yes == 'closed' ->
			Al_St_yes = (Al_St_yes_Ter, Al_St_yes_Num), 
			YES = ['al', Al_Cl_yes, Al_St_yes_Ter, Al_St_yes_Num],
			Tree_yes = Al_Tr_yes
		; ( St_yes = (Ter1, N1) -> atomic_list_concat([Ter1,N1], St_yes0); St_yes0 = St_yes ),
		  YES = ['na', Cl_yes, St_yes0],
		  Tree_yes = Tr_yes
		),
		( Al_Cl_no ==  'closed' ->
			Al_St_no = (Al_St_no_Ter, Al_St_no_Num),
			NO  = ['al', Al_Cl_no,  Al_St_no_Ter, Al_St_no_Num],
			Tree_no = Al_Tr_no
		; ( St_no = (Ter2, N2) -> atomic_list_concat([Ter2,N2], St_no0); St_no0 = St_no ),
		  NO  = ['na', Cl_no,  St_no0],
		  Tree_no = Tr_no
		),
		atomic_list_concat(['yes' | YES], '_', Yes_File),
		atomic_list_concat([ 'no' | NO],  '_', No_File),
		( memberchk([Al,'closed'|_], [YES,NO]) ->
			memberchk(Al-Align, ['al'-'align', 'na'-'no_align']),
			write_parsed_problem(S, Format, Align, ID)
		; write_parsed_problem(S, Format, 'no_align', ID)
		),
		write_proof_tree(S, Format, Tree_yes, ID),
		write_proof_tree(S, Format, Tree_no,  ID),
		( Format == 'xml' -> format('~w, ~w~n', [Yes_File, No_File]); true )
	; YES = 'yes_NA', NO = 'no_NA',
		write_parsed_problem(S, Format, 'no_align', ID),
		( Format == 'xml' ->
			write(S, '\n<tableau>no tableau</tableau>\n<tableau>no tableau</tableau>\n'),
		 	format('~w, ~w~n', [YES, NO])
		; true )
	),
	close(S).

% writing proof trees in xml or json format
write_proof_tree(S, 'xml', Tree, PID) :- !,
	write_xml_proof_tree(S, Tree, PID).

write_proof_tree(S, 'json', Tree, PID) :- !,
	write_json_proof_tree(S, Tree, PID).

write_parsed_problem(S, 'xml', Align, ID) :- !,
	write_parsed_problem_as_xml(S, Align, ID).

write_parsed_problem(S, 'json', Align, ID) :- !,
	write_parsed_problem_as_json(S, Align, ID).	


print_problem(ID) :-
	findall(Prem, sen_id(_, ID, 'p', _, Prem), Prems),
	( sen_id(_, ID, 'h', Ans, Hypo) ->
		report(['ID = ', ID, ',   Gold Answer = ', Ans]),
		atomic_list_concat(Prems, '\n', Prems1),
		format('  ~w~n? ~w~n', [Prems1, Hypo])
	; report(['There is no problem with ID=', ID, ' in the selected data set'])
	).
