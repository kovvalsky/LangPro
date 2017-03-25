%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Description: XML output for LLFs and Proofs
% 	   Author: lasha.abzianidze{at}gmail.com 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%    XML Output of trees, terms and LLFs
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Write CCG trees, CCG terms and LLFs 
% of RTE Problems in the XML files
xml_probs_llfs(Prob_IDs) :-
	xml_probs_llfs(Prob_IDs, 'RTE_to_LLF'). 

xml_probs_llfs(Prob_IDs, XMLFile) :-
	( exists_directory('xml') -> true; make_directory('xml') ),
	atomic_list_concat(['xml/', XMLFile, '.xml'], FullFileName), 
	open(FullFileName, write, S, [encoding(utf8)]),
	write(S, '<?xml version="1.0" encoding="UTF-8"?>\n'),
	write(S, '<?xml-stylesheet type="text/xsl" href="xsl_dtd/ttterms.xsl"?>\n'),
	write(S, '<parsed_problems>\n'),
	maplist( write_parsed_problem_as_xml(S, 'no_align'), Prob_IDs ),
	write(S, '</parsed_problems>\n'),
	close(S),
	atomic_list_concat(['xsltproc --maxparserdepth 1000000 --maxdepth 1000000 ', FullFileName, ' -o ', 'xml/', XMLFile, '.html'], ShellCommand),
	%shell('xsltproc xml/tableau.xml -o xml/tableau.html').	
	shell(ShellCommand).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Given SenIDs, write corresponding CCG trees,
% CCG terms and LLFs in a XML file
xml_senIDs_llfs(List_Int) :- 
	xml_senIDs_llfs(List_Int, 'CCG_to_LLF').

xml_senIDs_llfs(List_Int, XMLFile) :-
	listInt_to_id_ccgs(List_Int, CCG_IDs),
	( exists_directory('xml') -> true; make_directory('xml') ),
	atomic_list_concat(['xml/', XMLFile, '.xml'], FullFileName), 
	open(FullFileName, write, S, [encoding(utf8)]),
	write(S, '<?xml version="1.0" encoding="UTF-8"?>\n'),
	write(S, '<?xml-stylesheet type="text/xsl" href="xsl_dtd/ttterms.xsl"?>\n'),
	write(S, '<parsed_sentences>\n'),
	xml_ccgIDs_to_llfs(S, CCG_IDs ),
	write(S, '</parsed_sentences>\n'),
	close(S),
	atomic_list_concat(['xsltproc --maxparserdepth 1000000 --maxdepth 1000000 ', FullFileName, ' -o ', 'xml/', XMLFile, '.html'], ShellCommand),
	%shell('xsltproc xml/tableau.xml -o xml/tableau.html').	
	shell(ShellCommand).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%      XML output for a tableau proof
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
output_XML(Tree, Problem_Id, FileName) :-
	retract(tree_structure(_)),
	asserta(tree_structure(Tree)),
	(exists_directory('xml') -> true; make_directory('xml')),
	atomic_list_concat(['xml/', FileName, '.xml'], FullFileName), 
	open(FullFileName, write, S, [encoding(utf8)]),
	write(S, '<?xml version="1.0" encoding="UTF-8"?>\n'),
	write(S, '<?xml-stylesheet type="text/xsl" href="xsl_dtd/tableau.xsl"?>\n'),
	write(S, '<!DOCTYPE tableau SYSTEM "xsl_dtd/tableau.dtd">\n'),
	write(S, '<tableau>\n'),

	write_XML_problem(S, Problem_Id), !, 
	
	write_tree_elements(S, [Tree]),	

	write(S, '</tableau>'),
	close(S),
	!,
	atomic_list_concat(['xsltproc --maxparserdepth 1000000 --maxdepth 1000000 ', FullFileName, ' -o ', 'xml/', FileName, '.html'], ShellCommand),
	%shell('xsltproc xml/tableau.xml -o xml/tableau.html').	
	shell(ShellCommand).


print_XML(Tree, Problem_Id) :-
	retract(tree_structure(_)),
	asserta(tree_structure(Tree)),
	current_output(S),
	%write(S, '<?xml version="1.0" encoding="UTF-8"?>\n'),
	%write(S, '<?xml-stylesheet type="text/xsl" href="xsl_dtd/tableau.xsl"?>\n'),
	%write(S, '<!DOCTYPE tableau SYSTEM "xsl_dtd/tableau.dtd">\n'),
	write(S, '<tableau>\n'),
	write_XML_problem(S, Problem_Id), !, 
	write_tree_elements(S, [Tree]),	
	write(S, '</tableau>'),
	%close(S),
	!.

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
		write(S, '<subTrees>\n'),
		write_tree_elements(S, Children),
		write(S, '</subTrees>\n')
	  ; true
	),
	write(S, '</tree>\n'),
	write_tree_elements(S, Rest).

write_tree_elements(S, closer(IDs)) :-
	IDs = [ClIDs, ClRule],
	write(S, '<tree>\n<node>\n<closer>\n'),
	term_to_atom(ClIDs, AtClIDs),
	atomic_list_concat(['<closer_ids>', AtClIDs, '</closer_ids>\n', '<closer_rule>', ClRule, '</closer_rule>\n'], Write),
	write(S, Write),
	write(S, '</closer>\n</node>\n</tree>\n').
	

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
	term_to_atom(RuleApp, RuleAppAtom),
	atomic_list_concat(['<source rule="', RuleId, '" ruleApp="', RuleAppAtom, '" >\n'], SourceBegTag),
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






%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%  Parsed Problem to XML
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%	( exists_directory('xml') -> true; make_directory('xml') ),
%	atomic_list_concat(['xml/', FileName, '.xml'], FullFileName), 
%	open(FullFileName, write, S, [encoding(utf8)]),
%	write(S, '<?xml version="1.0" encoding="UTF-8"?>\n'),
%	write(S, '<?xml-stylesheet type="text/xsl" href="xsl_dtd/ttterms.xsl"?>\n'),
%	write(S, '<!DOCTYPE ttterms SYSTEM "xsl_dtd/ttterms.dtd">\n'),


write_parsed_problem_as_xml(S, Align, ProbID) :-
	findall( X, sen_id(X, ProbID, _, _, _), IDs),
	format(S, '<parsed_problem probID="~w">\n', [ProbID]),
	%free_vars_to_indexed_atoms('x', TTterms, PrettyTTterms),
	findall(ccg(X, CCG), (member(X, IDs), ccg(X, CCG)), CCG_IDs),
	maplist(ccgIDTree_to_ccgIDTerm, CCG_IDs, CCGTerms_IDs),
	maplist(nth1_projection(2), CCGTerms_IDs, CCGTerms),
	maplist(ne_ccg, CCGTerms, CCGTerms_ne),
	maplist(clean_ccgTerm_once, CCGTerms_ne, CCGTerms_clean),
	maplist(correct_ccgTerm, CCGTerms_clean, CCGTerms_corr),
	maplist(once_gen_quant_tt, CCGTerms_corr, _LLFs),
	problem_to_ttTerms(Align, ProbID, PremLLFs, HypLLF, Al_PremLLFs, Al_HypLLF, _KB), 
	% test
	( Align = align ->
		append(Al_PremLLFs, Al_HypLLF, FinLLFs)
	; 	append(PremLLFs, HypLLF, FinLLFs)
	),
	all_terms_per_sentence(IDs, CCG_IDs, CCGTerms, CCGTerms_corr, FinLLFs, List),
	maplist(parsed_sen_to_xml_format(S), List),
	write(S, '</parsed_problem>\n\n').
	%close(S).

xml_ccgIDs_to_llfs(S, CCG_IDs) :-
	maplist(ccgIDTree_to_ccgIDTerm, CCG_IDs, CCGTerms_IDs),
	maplist(nth1_projection(1), CCGTerms_IDs, IDs),
	maplist(nth1_projection(2), CCGTerms_IDs, CCGTerms),
	maplist(ne_ccg, CCGTerms, CCGTerms_ne),
	maplist(clean_ccgTerm_once, CCGTerms_ne, CCGTerms_clean),
	maplist(correct_ccgTerm, CCGTerms_clean, CCGTerms_corr),
	maplist(once_gen_quant_tt, CCGTerms_corr, LLFs),
	all_terms_per_sentence(IDs, CCG_IDs, CCGTerms, CCGTerms_corr, LLFs, List),
	maplist(parsed_sen_to_xml_format(S), List).



% given IDs, CCG tems, ... LLFs return a list per sentence
all_terms_per_sentence([ID | Rest], CCG_IDs, CCGTerms, CCGTerms_corr, LLFs, List) :-
	!, 
	sen_id(ID, _, PHdw, _, Sent),
	upcase_atom(PHdw, PH),
	atomic_list_concat([PH,'<sub>',ID,'</sub>'], PHID),
	( nth1(I, CCG_IDs, ccg(ID, CCG)) ->
		nth1(I, CCGTerms, CCGTerm),
		nth1(I, CCGTerms_corr, CCGTerm_corr),
		nth1(I, LLFs, LLF),
		Term_List = [CCG, CCGTerm, CCGTerm_corr, LLF]
	; Term_List = []
	),
	List = [[PHID, Sent | Term_List] | Rest_List],
	all_terms_per_sentence(Rest, CCG_IDs, CCGTerms, CCGTerms_corr, LLFs, Rest_List). 
		 
			
all_terms_per_sentence([], _, _, _, _, []).

	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% format a sentence as xml
parsed_sen_to_xml_format(S, [ID, Sent | Terms ]) :-
	write(S, '<parsed_sentence>\n'),
	format(S, '<id_sent>~w: ~w</id_sent>~n', [ID, Sent]),
	( Terms = [CCG, CCGTerm, CCGTerm_corr, LLF] ->  
		% print tt terms
		maplist(pretty_vars_in_ttterm(1-1), _, [CCGTerm, CCGTerm_corr, LLF], [Pr_CCGTerm, Pr_CCGTerm_corr, Pr_LLF]),
		ccgTree_to_xml_format(S, CCG),
		write(S, '<ccgterm>\n'),   
		ttTerm_to_xml(S, Pr_CCGTerm),
		write(S, '</ccgterm>\n\n<corr_ccgterm>\n'),
		ttTerm_to_xml(S, Pr_CCGTerm_corr),
		write(S, '</corr_ccgterm>\n\n<llf>\n'),
		ttTerm_to_xml(S, Pr_LLF),
		write(S, '</llf>\n\n')
	; format(S, '~w~n', ['Warning: Sentence could not be parsed\n'])
	),
	write(S, '</parsed_sentence>\n').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ttTerm to XML
ttTerm_to_xml(S, (X,Ty)) :-
	var(X) -> 
		report(["Error: unexpected Var while converting ttTerm into XML"]), fail
	; atom(X), (atom_chars(X, ['x'|_]); atom_chars(X,['p'|_])) -> %variable
		term_to_atom(X, AtX),
		type_to_xml(Ty, AtTy),
		atomic_list_concat(['<ttterm>\n<var>', AtX, '</var>\n<type>', AtTy, '</type>\n</ttterm>\n'], Atom),
		write(S, Atom)
	; X = tlp(Tk,Lm,Pos,_,Ne) -> %constant
		type_to_xml(Ty, AtTy),
		atomic_list_concat(['<ttterm>\n<tlp>\n<tok>',Tk,'</tok>\n<lem>',Lm,'</lem>\n<pos>',Pos,'</pos>\n<ner>',Ne,'</ner>\n</tlp>\n<type>', AtTy, '</type>\n</ttterm>\n'], Atom),	
		write(S, Atom)
	; X = TT1 @ TT2 -> %application
		write(S, '<ttterm>\n<app>\n'),
		ttTerm_to_xml(S, TT1),
		ttTerm_to_xml(S, TT2),
		type_to_xml(Ty, AtTy),
		atomic_list_concat(['</app>\n<type>', AtTy, '</type>\n</ttterm>\n'], Atom),	
		write(S, Atom)
	; X = abst(Y, TT) -> %abstraction
		write(S, '<ttterm>\n<abst>\n'),
		ttTerm_to_xml(S, Y),
		ttTerm_to_xml(S, TT),
		type_to_xml(Ty, AtTy),
		atomic_list_concat(['</abst>\n<type>', AtTy, '</type>\n</ttterm>\n'], Atom),	
		write(S, Atom)
	; X = (E, Ty1) -> %type changing
		write(S, '<ttterm>\n'),
		ttTerm_to_xml(S, (E,Ty1)),
		type_to_xml(Ty, AtTy),
		atomic_list_concat(['<type>', AtTy, '</type>\n</ttterm>\n'], Atom),	
		write(S, Atom)  
	; report(["Error: unexpected clause while converting ttTerm into XML"]), fail.



% convert type into atom for html printing
type_to_xml(Type, HTML) :-
	var(Type) ->
		report(["Error: unexpected type while converting into XML"])
	; atom(Type) ->
		HTML = Type
	; Type = A:B ->
		(var(B) -> 
			HTML = A
		; atomic_list_concat([A,'<tyfeat>',B,'</tyfeat>'], HTML) 
		)
	; Type = np:A~>s:B, var(A) ->
		( var(B) -> Feat = ''; atomic_list_concat(['<tyfeat>',B,'</tyfeat>'], Feat)  ),
		atomic_list_concat(['vp',Feat], HTML)
	; Type = A~>B ->
		type_to_xml(A, AtA),
		type_to_xml(B, AtB),
		( A = _~>_, \+((A = np:F~>s:_, var(F))) -> 
			atomic_list_concat(['(',AtA,'),',AtB], HTML)
		; atomic_list_concat([AtA,',',AtB], HTML) 
		)
	; report(["Error: unexpected type while converting into XML"]).    
	
	


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%  CCGtree to XML
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

write_CCGtrees_as_xml(CCGtrees, FileName) :-
	(exists_directory('xml') -> true; make_directory('xml')),
	atomic_list_concat(['xml/', FileName, '.xml'], FullFileName), 
	open(FullFileName, write, S, [encoding(utf8)]),
	write(S, '<?xml version="1.0" encoding="UTF-8"?>\n'),
	write(S, '<?xml-stylesheet type="text/xsl" href="xsl_dtd/ccgtrees.xsl"?>\n'),
	write(S, '<!DOCTYPE ccgtrees SYSTEM "xsl_dtd/ccgtrees.dtd">\n'),
	write(S, '<ccgtrees>\n'),
	maplist(ccgTree_to_xml_format(S), CCGtrees),
	write(S, '</ccgtrees>\n\n'),
	close(S).
	%!,
	%atomic_list_concat(['xsltproc --maxparserdepth 1000000 --maxdepth 1000000 ', FullFileName, ' -o ', 'xml/', FileName, '.html'], ShellCommand),
	%shell('xsltproc xml/tableau.xml -o xml/tableau.html').	
	%shell(ShellCommand).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% full ccgTree into xml
ccgTree_to_xml_format(S, Tree) :-
	write(S, '<ccgtree>\n'),
	ccgTree_to_xml(S, Tree),
	write(S, '</ccgtree>\n\n').


ccgTree_to_xml(S, Tree) :-
	Tree = t(Cat, Tk, Lm, Pos, _, Ner) -> % leaf
		cat_to_xml(Cat, AtCat),
		atomic_list_concat(['<leaf>\n<tok>',Tk,'</tok>\n<lem>',Lm,'</lem>\n<pos>',Pos,'</pos>\n<ner>',Ner,'</ner>\n<cat>',AtCat,'</cat>\n</leaf>'], Atom),
		write(S, Atom)
	; (Tree =.. [Urule, Cat, _, T]; Tree =.. [Urule, Cat, T]),  % unary rules
	  memberchk(Urule, [lx, tr]) ->
		write(S, '<unary>\n'),
		ccgTree_to_xml(S, T),
		cat_to_xml(Cat, AtCat),
		atomic_list_concat(['<cat>',AtCat,'</cat>\n<rule>',Urule,'</rule>\n</unary>\n'], Atom), 
		write(S, Atom)
	; (Tree =.. [Brule, Cat, T1, T2]; Tree =.. [Brule, Cat, _, T1, T2]),  % binary rules
	  memberchk(Brule, [fa, ba, fc, bc, fxc, bxc, lp, rp, ltc, rtc, gbc, gfc, gbxc, gfxc]) ->
		write(S, '<binary>\n'),
		ccgTree_to_xml(S, T1),
		ccgTree_to_xml(S, T2),
		cat_to_xml(Cat, AtCat),
		atomic_list_concat(['<cat>',AtCat,'</cat>\n<rule>',Brule,'</rule>\n</binary>\n'], Atom), 
		write(S, Atom)
	; Tree = conj(Cat, _, T1, T2) -> % conjunction
		write(S, '<binary>\n'),
		ccgTree_to_xml(S, T1),
		ccgTree_to_xml(S, T2),
		cat_to_xml(Cat, AtCat),
		atomic_list_concat(['<cat>',AtCat,'</cat>\n<rule>cnj</rule>\n</binary>\n'], Atom), 
		write(S, Atom)  		
	; report(["Error: unexpected clause while converting CCGtree into XML"]).



% convert category into atom for html printing
cat_to_xml(Cat, HTML) :-
	var(Cat) ->
		report(["Error: unexpected type while converting into XML"])
	; atom(Cat) ->
		string_upper(Cat, HTML)
	; Cat = A:B ->
		(var(B) -> 
			string_upper(A, HTML)
		; string_upper(A, UpA),
		  atomic_list_concat([UpA,'<tyfeat>',B,'</tyfeat>'], HTML) 
		)
	; memberchk(Cat, [s/np, (s:B)/np, s/(np:X), (s:B)/(np:X), s\np, (s:B)\np, s\(np:X), (s:B)\(np:X)]), var(X) ->
		( var(B) -> Feat = ''; atomic_list_concat(['<tyfeat>',B,'</tyfeat>'], Feat) ),
		atomic_list_concat(['VP',Feat], HTML)
	; Cat =.. [Func,A,B] ->
		%(Func = '\\' -> Functor = '\\\\'; Functor = Func ),
		cat_to_xml(A, AtA),
		cat_to_xml(B, AtB),
		( A =.. [F,A1,A2], F\=':', \+((memberchk(A2-(A1), [np-s, np-(s:_), (np:X)-s, (np:X)-(s:_)]), var(X))) -> 
			atomic_list_concat(['(',AtA,')',Func,AtB], HTML)
		; atomic_list_concat([AtA,Func,AtB], HTML) 
		)
	; report(["Error: unexpected Category while converting into XML"]).










