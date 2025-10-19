%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Contains predicates used for online version
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module('../xml/xml_output', [write_parsed_problem_as_xml/3, write_xml_proof_tree/3]).
:- use_module('../json/json_output', [parsed_problem_to_dict/3]).
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
	problem_to_ttTerms('align', ID, Prems, Hypos, Align_Prems, Align_Hypos, KB),
	set_rule_eff_order,
	check_problem(KB-_, Align_Prems, Align_Hypos, 'yes', _, Al_Cl_yes, Al_St_yes, _, Al_Tr_yes),
	( Al_St_yes \== 'Defected' ->
		check_problem(KB-_, Align_Prems, Align_Hypos, 'no', _,  Al_Cl_no, Al_St_no, _, Al_Tr_no),
		check_problem(KB-_, Prems, Hypos, 'yes', _, Cl_yes, St_yes, _, Tr_yes),
		check_problem(KB-_, Prems, Hypos, 'no', _,  Cl_no, St_no, _, Tr_no),
		summarize_align_closed_status(Al_Cl_yes, Al_St_yes, Al_Tr_yes, Cl_yes, St_yes, Tr_yes, YES, Tree_yes),
		summarize_align_closed_status(Al_Cl_no, Al_St_no, Al_Tr_no, Cl_no, St_no, Tr_no, NO, Tree_no),
		( memberchk([Al,'closed'|_], [YES,NO]) ->
			memberchk(Al-Align, ['al'-'align', 'na'-'no_align'])
		; 	Align = 'no_align'
		)
	; YES = 'yes_NA', NO = 'no_NA', Align = 'no_align'
	),
	write_problem_proof(Format, YES, NO, Align, Tree_yes, Tree_no, KB, ID).

% sumarizes the results with aligned and non-aligned terms
summarize_align_closed_status(Al_Cl, Al_St, Al_Tr, Cl, St, Tr, Ans, Tree) :-
	( Al_Cl == 'closed' ->
		Al_St = (Al_St_Ter, Al_St_Num), 
		Ans = ['al', Al_Cl, Al_St_Ter, Al_St_Num],
		Tree = Al_Tr
	; ( St = (Ter1, N1) -> atomic_list_concat([Ter1,N1], St0); St0 = St ),
		Ans = ['na', Cl, St0],
		Tree = Tr
	).

write_problem_proof('xml', YES, NO, Align, Tree_yes, Tree_no, KB, ID) :-
	current_output(S),
	format(S, 'KB: ~w~n', [KB]),
	write_parsed_problem_as_xml(S, Align, ID),
	( YES \== 'yes_NA' ->
		write_xml_proof_tree(S, Tree_yes, ID),
		write_xml_proof_tree(S, Tree_no, ID),
		atomic_list_concat(['yes' | YES], '_', Yes_File),
		atomic_list_concat([ 'no' | NO],  '_', No_File),
		format(S, '~w, ~w~n', [Yes_File, No_File])
	; write(S, '\n<tableau>no tableau</tableau>\n<tableau>no tableau</tableau>\n'),
		format(S, '~w, ~w~n', [YES, NO])
	),
	close(S).

% {prob_id:ID, prob:ListProbDict, aligned_llfs:Align, 
%  proofs:{entailment:{info:Yes, proof:Tree_yes}, contradiction:{info:No, proof:Tree_no}}}
write_problem_proof(json(Width,Step,Tab), YES, NO, Align, Tree_yes, Tree_no, KB, ID) :-
	current_output(S),
	parsed_problem_to_dict(Align, ID, ProbDict),
	term_to_json(KB, KB_J),
	ProbDict1 = ProbDict.put([kb=KB_J]),
	( YES \== 'yes_NA' ->
		maplist(term_to_json, 	[YES, NO, Tree_yes, Tree_no], 
								[YES_J, NO_J, Tree_yes_J, Tree_no_J]), 
		ProbProofDict = ProbDict1.put([proofs=_{
			entailment:j{info:YES_J, proof:Tree_yes_J},
			contradiction:j{info:NO_J, proof:Tree_no_J}
			}])
	; ProbProofDict = ProbDict1
	),
	json_write(S, ProbProofDict, [width(Width), step(Step), tab(Tab)]),
	nl(S), close(S).


print_problem(ID) :-
	findall(Prem, sen_id(_, ID, 'p', _, Prem), Prems),
	( sen_id(_, ID, 'h', Ans, Hypo) ->
		report(['ID = ', ID, ',   Gold Answer = ', Ans]),
		atomic_list_concat(Prems, '\n', Prems1),
		format('  ~w~n? ~w~n', [Prems1, Hypo])
	; report(['There is no problem with ID=', ID, ' in the selected data set'])
	).
