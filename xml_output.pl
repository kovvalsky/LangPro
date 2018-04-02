%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Description: XML output for Tableau Tree
%     Version: 13.12.29
%      Author: lasha.abzianidze{at}gmail.com 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

output_XML(Tree, Problem_Id, FileName) :-
	retract(tree_structure(_)),
	asserta(tree_structure(Tree)),
	(exists_directory('xml') -> true; make_directory('xml')),
	atomic_list_concat(['xml/', FileName, '.xml'], FullFileName), 
	open(FullFileName, write, S, [encoding(utf8)]),
	write(S, '<?xml version="1.0" encoding="UTF-8"?>\n'),
	write(S, '<?xml-stylesheet type="text/xsl" href="tableau.xsl"?>\n'),
	write(S, '<!DOCTYPE tableau SYSTEM "tableau.dtd">\n'),
	write(S, '<tableau>\n'),

	write_XML_problem(S, Problem_Id), !, 
	
	write_tree_elements(S, [Tree]),	

	write(S, '</tableau>'),
	close(S),
	!,
	atomic_list_concat(['xsltproc --maxparserdepth 1000000 ', FullFileName, ' -o ', 'xml/', FileName, '.html'], ShellCommand),
	%shell('xsltproc xml/tableau.xml -o xml/tableau.html').	
	shell(ShellCommand).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
write_XML_problem(S, Problem_Id) :-
	sen_id(_, Problem_Id, _, Answer, _), !,
	atomic_list_concat(['<problem id="', Problem_Id, '" answer="', Answer, '" >\n'], ProbBegTag),
	write(S, ProbBegTag),
	findall((Id, Type, Sent), sen_id(Id, Problem_Id, Type, Answer, Sent), List),
	write_XML_prem_con(S, List),
	write(S, '</problem>\n').

write_XML_prem_con(S, [(Id, Type, Sent) | Rest]) :-
	( Type == 'p' ->
		atomic_list_concat(['<premise id="', Id, '" >', Sent, '</premise>\n'], PremEl),
		write(S, PremEl);
	  Type == 'h' ->
		atomic_list_concat(['<conclusion id="', Id, '" >', Sent, '</conclusion>\n'], ConEl),
		write(S, ConEl);
	  write('Error in write_XML_prem_con') ),
	write_XML_prem_con(S, Rest).
		
write_XML_prem_con(_, []).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% tree elements
write_tree_elements(S, [Tree | Rest]) :-	
	write(S, '<tree>\n'),
	Tree = tree(Root, Children),
	write_node_element(S, Root),
	( nonvar(Children) -> 
		write_tree_elements(S, Children)
	  ; true
	),
	write(S, '</tree>\n'),
	write_tree_elements(S, Rest).

write_tree_elements(S, closer(IDs)) :-
	write(S, '<tree>\n'),
	write(S, '<node>\n'),
	write(S, '<closer>\n'),
	term_to_atom(IDs, Text),
	write(S, Text),
	write(S, '\n</closer>\n'),
	write(S, '</node>\n'),
	write(S, '</tree>\n').
	

write_tree_elements(S, 'Model') :-
	write(S, '<tree>\n'),
	write(S, '<node>\n'),
	write(S, '<model>\n'),
	write(S, 'MODEL'),
	write(S, '\n</model>\n'),
	write(S, '</node>\n'),
	write(S, '</tree>\n').

write_tree_elements(_, []).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% node element
/*write_node_element(S, trnd(nd(TTterm, TTargs, Sign), 11, Note, _)) :-
	Node = trnd(nd(TTterm, TTargs, Sign), 11, Note, _),
	term_to_atom(Node, M), writeln(M),
	%Node = trnd(nd(TTterm, TTargs, Sign), Id, Note, _),
	atomic_list_concat(['<node absId="', 11, '" id="', 11, '" >\n'], NodeBegTag),
	write(S, NodeBegTag),
	atomic_list_concat(['<formula sign="', Sign, '" >\n'], FormulaBegTag),
	write(S, FormulaBegTag),
	write_llf_element(S, TTterm),
	write(S, '<argList>\n'), 
	write_arg_elements(S, TTargs),
	write(S, '</argList>\n'),	
	write(S, '</formula>\n'),
	write_source_element(S, Note),
	write(S, '</node>\n').*/

write_node_element(S, Node) :-
	%term_to_atom(Node, M), writeln(M),
	Node = trnd(nd(TTmods, TTterm, TTargs, Sign), Id, RuleApp, _),
	atomic_list_concat(['<node absId="', Id, '" id="', Id, '" >\n'], NodeBegTag),
	write(S, NodeBegTag),
	atomic_list_concat(['<formula sign="', Sign, '" >\n'], FormulaBegTag),
	write(S, FormulaBegTag),
	write(S, '<modList>\n'), 
	write_mod_elements(S, TTmods),
	write(S, '</modList>\n'),
	write_llf_element(S, TTterm),
	write(S, '<argList>\n'), 
	write_arg_elements(S, TTargs),
	write(S, '</argList>\n'),	
	write(S, '</formula>\n'),
	write_source_element(S, RuleApp),
	write(S, '</node>\n').

% for CLSING node
%write_node_element(S, closer(IDs)) :-


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% llf element
write_llf_element(S, TTterm) :-
	write(S, '<llf>'),
	ttTerm_to_prettyTerm(TTterm, LLF),
	term_to_atom(LLF, Atom1),
	atomic_list_concat(List1, 'abst(', Atom1),
	atomic_list_concat(List1, '(&#955;', AtomLLF),
	write(S, AtomLLF),
	write(S, '</llf>\n').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% arg elements
write_arg_elements(S, [TTarg | Rest]) :-
	write(S, '<arg>'),
	ttTerm_to_prettyTerm(TTarg, LLF),
	term_to_atom(LLF, Atom1),
	atomic_list_concat(List1, 'abst(', Atom1),
	atomic_list_concat(List1, '(&#955;', AtomLLF),
	write(S, AtomLLF),
	write(S, '</arg>\n'),
	write_arg_elements(S, Rest).

write_arg_elements(_, []).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% mod elements
write_mod_elements(S, [TTmod | Rest]) :-
	write(S, '<mod>'),
	ttTerm_to_prettyTerm(TTmod, LLF),
	term_to_atom(LLF, Atom1),
	atomic_list_concat(List1, 'abst(', Atom1),
	atomic_list_concat(List1, '(&#955;', AtomLLF),
	write(S, AtomLLF),
	write(S, '</mod>\n'),
	write_mod_elements(S, Rest).

write_mod_elements(_, []).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% source element
write_source_element(_S, []) :- 
	!.

write_source_element(S, RuleApp) :-
	( RuleApp =.. [RuleId, Ids];
	  RuleApp =.. [RuleId, Ids, Olds]
	), !,
	atomic_list_concat(['<source rule="', RuleId, '" >\n'], SourceBegTag),
	write(S, SourceBegTag),	
	write(S, '<idList>\n'),
	write_id_elements(S, Ids),
	write(S, '</idList>\n'),
	( var(Olds) ->
		true
	  ;	write(S, '<oldConstList>\n'),
		write_old_consts(S, Olds),
		write(S, '</oldConstList>\n')
	),
	write(S, '</source>\n').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% id elements
write_id_elements(S, [Id | Rest]) :-
	write(S, '<id>'),	
	write(S, Id),
	write(S, '</id>\n'),
	write_id_elements(S, Rest).
	
write_id_elements(_, []).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% old constants
write_old_consts(S, [C | Rest]) :-
	write(S, '<oldConst>'),	
	ttTerm_to_prettyTerm(C, C1),
	term_to_atom(C1, C2),
	write(S, C2),
	write(S, '</oldConst>\n'),
	write_id_elements(S, Rest).
	
write_old_consts(_, []).



