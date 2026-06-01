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
	online_demo(ID, [], Format).

online_demo(ID, IKB, Format) :-
	%report(['Entering online_demo/1\n']),
	%entail(1, _Answer, Provers_Answer, Closed, FinalStatus),
	%print_problem(ID),
	( debMode('proof_tree') -> true; assertz(debMode('proof_tree')) ), % for building trees
	problem_to_ttTerms('align', ID, Prems, Hypos, Align_Prems, Align_Hypos, OKB),
	append(IKB, OKB, KB), % merge initial and obtained KBs
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
	write_problem_parse_and_proof(Format, YES, NO, Align, Tree_yes, Tree_no, KB, ID).

% summarizes the results with aligned and non-aligned terms
summarize_align_closed_status(Al_Cl, Al_St, Al_Tr, Cl, St, Tr, Ans, Tree) :-
	( Al_Cl == 'closed' ->
		Al_St = (Al_St_Ter, Al_St_Num),
		Ans = ['al', Al_Cl, Al_St_Ter, Al_St_Num],
		Tree = Al_Tr
	; ( St = (Ter1, N1) -> atomic_list_concat([Ter1,N1], St0); St0 = St ),
		Ans = ['na', Cl, St0],
		Tree = Tr
	).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Writes the problem related parses and proofs in the specified format (xml or json)

% write parses and proofs in xml format to the current output
write_problem_parse_and_proof('xml', YES, NO, Align, Tree_yes, Tree_no, KB, ID) :-
	current_output(S),
	write_problem_parse_and_proof_to_stream(S, YES, NO, Align, Tree_yes, Tree_no, KB, ID).

% write parses and proofs in xml format to the xml file, which is created or overwritten
write_problem_parse_and_proof(XMLFile, YES, NO, Align, Tree_yes, Tree_no, KB, ID) :-
    atom(XMLFile),
	file_name_extension(_, 'xml', XMLFile), !,
	% if XMLFile is a pattern with a problem ID
    ( sub_atom(XMLFile, _, _, _, '~w')
    ->  format(atom(ExpandedFile), XMLFile, [ID])
    ;   ExpandedFile = XMLFile
    ),
	atomic_list_concat(['xml/', ExpandedFile], FullFileName),
    setup_call_cleanup(
        open(FullFileName, write, S, [encoding(utf8)]),
		(
			% write the XML header and XSL & DTD references
			write(S, '<?xml version="1.0" encoding="UTF-8"?>\n'),
			write(S, '<?xml-stylesheet type="text/xsl" href="xsl_dtd/combined.xsl"?>\n'),
			write_problem_parse_and_proof_to_stream(S, YES, NO, Align, Tree_yes, Tree_no, KB, ID)
		),
        close(S)
    ),
	( debMode('html') ->
		file_name_extension(BaseName, 'xml', ExpandedFile),
		atomic_list_concat(['xsltproc --maxparserdepth 1000000 --maxdepth 1000000 ', FullFileName, ' -o ', 'xml/', BaseName, '.html'], ShellCommand),
		%shell('xsltproc xml/tableau.xml -o xml/tableau.html').
		shell(ShellCommand)
	;  true
	).

% {prob_id:ID, prob:ListProbDict, aligned_llfs:Align,
%  proofs:{entailment:{info:Yes, proof:Tree_yes}, contradiction:{info:No, proof:Tree_no}}}
write_problem_parse_and_proof(json(Width,Step,Tab), YES, NO, Align, Tree_yes, Tree_no, KB, ID) :-
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


% auxiliary predicate for writing the proof in xml format to a stream
write_problem_parse_and_proof_to_stream(S, YES, NO, Align, Tree_yes, Tree_no, KB, ID) :-
	write(S, '\n<combined>\n'),
	% <parsed_problem id="ID">...</parsed_problem>
	write_parsed_problem_as_xml(S, Align, ID),
	% write the KB
	format(S, '<kb>~w</kb>~n', [KB]),
	% write tableau trees if there are any, otherwise write no tableau
	write(S, '\n<proof>\n'),
	atomic_list_concat(['yes' | YES], '_', Yes_File),
	format(S, '\n<tableau_label>~w</tableau_label>~n', [Yes_File]),
	( YES \== 'yes_NA'
	->  % entailment tableau <tableau>...</tableau>
		write_xml_proof_tree(S, Tree_yes, ID)
	; 	write(S, '\n<tableau>no tableau</tableau>\n')
	),
	atomic_list_concat(['no' | NO], '_', No_File),
	format(S, '\n<tableau_label>~w</tableau_label>~n', [No_File]),
	( NO \== 'no_NA'
	->  % contradiction tableau <tableau>...</tableau>
		write_xml_proof_tree(S, Tree_no, ID)
	; 	write(S, '\n<tableau>no tableau</tableau>\n')
	),
	write(S, '\n</proof>\n</combined>').



print_problem(ID) :-
	findall(Prem, sen_id(_, ID, 'p', _, Prem), Prems),
	( sen_id(_, ID, 'h', Ans, Hypo) ->
		report(['ID = ', ID, ',   Gold Answer = ', Ans]),
		atomic_list_concat(Prems, '\n', Prems1),
		format('  ~w~n? ~w~n', [Prems1, Hypo])
	; report(['There is no problem with ID=', ID, ' in the selected data set'])
	).
