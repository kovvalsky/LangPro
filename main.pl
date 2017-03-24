:- op(601, xfx, (/)).
:- op(601, xfx, (\)).

:- ensure_loaded([lambda_tt,
				  lambda,
				  lexicon,
				  online_demo,
				  latex_ccgtree,
				  %term_query,
				  ttterm_to_term,
				  latex_ttterm,
				  ccg_term,
				  ccgTerm_to_ttTerm,
				  ccgTerm_to_llf,
				  gen_quant,
				  correct_term,
				  aligner,
				  ner,
				  extract,
				  sent_sim,	
				  bag_of_words,	
				  ling,
				  %nattableau,
				  tt_nattableau,
				  ttterm_preds,	
				  type_hierarchy,		
				  assign_term, % assigns a term to tlp
				  recognize_MWE,
				  annotate,	
				  wn_preds,	
				  tableau_tree,	
				  entail				  			
				 ]).

%:- dynamic latex_file_stream/1.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% returns sentence id list from problem id list
probIDs_to_senIDs([Prob_ID | Prob_Rest], Sen_IDs) :-
	!, findall(ID, sen_id(ID, Prob_ID,_,_,_), IDs),
	probIDs_to_senIDs(Prob_Rest, Sen_Rest),
	append(IDs, Sen_Rest, Sen_IDs).
	
probIDs_to_senIDs([], []).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% List_Int of senIDs into a list of (ID, CCG tree)-s
listInt_to_id_ccgs(List_Int, CCGs) :-
	( is_list(List_Int) ->
		findall(ccg(Id, Tree), (member(Id, List_Int), ccg(Id, Tree)), CCGs)
	; List_Int = Inf-Sup ->
		( nonvar(Inf), nonvar(Sup) -> findall(ccg(Id, Tree), (between(Inf, Sup, Id), ccg(Id, Tree)) , CCGs);
	 	  nonvar(Inf) -> findall(ccg(Id, Tree), (ccg(Id, Tree), Inf =< Id), CCGs);
		  nonvar(Sup) -> findall(ccg(Id, Tree), (ccg(Id, Tree), Sup >= Id), CCGs);
	 	  findall(ccg(Id, Tree), ccg(Id, Tree), CCGs) 
		)
	; report(["Error: Wrong format of the argument: ", List_Int]),
	  fail	 
	).


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
	write(S, '<?xml-stylesheet type="text/xsl" href="ttterms.xsl"?>\n'),
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
	write(S, '<?xml-stylesheet type="text/xsl" href="ttterms.xsl"?>\n'),
	write(S, '<parsed_sentences>\n'),
	xml_ccgIDs_to_llfs(S, CCG_IDs ),
	write(S, '</parsed_sentences>\n'),
	close(S),
	atomic_list_concat(['xsltproc --maxparserdepth 1000000 --maxdepth 1000000 ', FullFileName, ' -o ', 'xml/', XMLFile, '.html'], ShellCommand),
	%shell('xsltproc xml/tableau.xml -o xml/tableau.html').	
	shell(ShellCommand).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%               LaTeX Output
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Print CCG trees, CCG terms and LLFS 
% of the list of RTE problems into a Latex file
latex_probs_llfs(Prob_IDs) :-
	latex_probs_llfs(Prob_IDs, 'RTE_to_LLF'). 

latex_probs_llfs(Prob_IDs, LaTeXFile) :-
	probIDs_to_senIDs(Prob_IDs, Sen_IDs),
	latex_senIDs_llfs(Sen_IDs, LaTeXFile).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Given SenIDs, write corresponding CCG trees,
% CCG terms and LLFs in a Latex file
latex_senIDs_llfs(List_Int) :- 
	latex_senIDs_llfs(List_Int, 'CCG_to_LLF').

latex_senIDs_llfs(List_Int, LaTeXFile) :-
	listInt_to_id_ccgs(List_Int, CCG_IDs),
	( exists_directory('latex') -> true; make_directory('latex') ),
	atomic_list_concat(['latex/', LaTeXFile, '.tex'], FilePath), 
	open(FilePath, write, S, [encoding(utf8), close_on_abort(true)]),
	%asserta(latex_file_stream(S)),
	latex_ttTerm_preambule(S),
	write(S, '\\begin{document}\n'),
	%retractall(event_index), % temporarily here
	%maplist(ccg_to_lambda_term_latex(S), CCG_IDs, TTterm_IDs), % for ttterms solution 1
	maplist(latex_ccgID_llfs(S), CCG_IDs, TTterm_IDs), 
	!,
	write(S, '\\end{document}'),
	close(S),
	findall(ccg(Id, TTterm), (member(ccg(Id, TTterm), TTterm_IDs), nonvar(TTterm)), WF_TTterms),	
	length(WF_TTterms, Num), 
	%findall(XX, member(ccg(XX, _), WF_TTterms), Output), write(Output),
	length(TTterm_IDs, Total),
	format(atom(Per), '~2f', [Num * 100 / Total]),
	atomic_list_concat([Per, '% (', Num, ' from ', Total, ') of LLFs were generated\n'], Message),
	write(Message).	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% writes a CCG tree, a CCG term, a corrected CCG term
% and LLF(s) in a stream and returns LLF(s)_ID
latex_ccgID_llfs(S, CCG_ID, TTterm_ID) :-
	CCG_ID = ccg(Id, CCGTree),
	TTterm_ID = ccg(Id, GQTT), 
	( debMode('pr_sen') -> sen_id(Id,_,_,_,Sen), report([Id,': ',Sen]); true ),
	report([Id]),
	% print sentence and CCGtree
	sen_id_latex(S, Id),	
	ccgTree_to_tikzpicture(S, CCGTree), 				% print
	% CCGtree to ccgTerm
	ccgIDTree_to_ccgIDTerm(CCG_ID, ccg(Id, CCGTerm)),
	latex_ttTerm_print_tree(S, 2, CCGTerm), 			% print
	ne_ccg(CCGTerm, CCGTerm_1),
	%latex_ttTerm_print_tree(S, 6, CCGTerm_1), 			% print
	clean_ccgTerm_once(CCGTerm_1, CCGTerm_2),
	%latex_ttTerm_print_tree(S, 6, CCGTerm_2),			% print 
	CCGTerm_final = CCGTerm_2,
	correct_ccgTerm(CCGTerm_final, Corr_CCGTerm_final),
	print_used_lexical_rules(Id, Corr_CCGTerm_final),	% print
	latex_ttTerm_print_tree(S, 2, Corr_CCGTerm_final),	% print
	%% gen_quant_tt(Corr_CCGTerm_final, GQTTs),			% sick-train 7618 loops here
	%% maplist( latex_ttTerm_print_tree(S, 2), GQTTs ),	% print all GQ versions
	%% GQTTs = [GQTT|_],
	%% maplist( ttTerm_to_latexTerm, GQTTs, LatexTerms), maplist( writeln(S), LatexTerms). 
	once_gen_quant_tt(Corr_CCGTerm_final, GQTT),
	ttTerm_to_latexTerm(GQTT, LatexTerm), writeln(S, LatexTerm), writeln(S, '\n'), % pronts first LLF as a term
	latex_ttTerm_print_tree(S, 6, GQTT).				% print the first GQ version





%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
ccg_to_ccg_term(CCG_ID) :-
	ccgIDTree_to_ccgIDTerm(CCG_ID, ccg(Id, CCGTerm)),
	ne_ccg(CCGTerm, CCGTerm_1),
	clean_ccgTerm_once(CCGTerm_1, CCGTerm_2),
	CCGTerm_final = CCGTerm_2,
	correct_ccgTerm(CCGTerm_final, Corr_CCGTerm_final),
	print_used_lexical_rules(Id, Corr_CCGTerm_final).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ccg_to_lambda_term_latex(S, CCG_ID, TTterm_ID)
% converst CCG_ID pair into CCGTerm, CCGTerm into ttTerms (may fail),
% then prints target sentence, CCG_ID, CCGterm, ttTerms in latex way on S chanelle 
ccg_to_lambda_term_latex(S, CCG_ID, TTterm_ID) :-
	CCG_ID = ccg(Id, CCGTree),
	% print sentence and CCGtree
	sen_id_latex(S, Id),	
	ccgTree_to_tikzpicture(S, CCGTree),
	% CCGtree to ccgTerm
	ccgIDTree_to_ccgIDTerm(CCG_ID, ccg(Id, CCGTerm)),
	ne_ccg(CCGTerm, CCGTerm_1),
	clean_ccgTerm_once(CCGTerm_1, CCGTerm_2),
	CCGTerm_final = CCGTerm_2,
	% print ccgTerm
	latex_ttTerm_print_tree(S, 6, CCGTerm_final), 
	%ignore(ccgTerms_to_ttTerms([CCG_ID_term_final], [TTterm_ID])),
	(	%getting TTterm
		ccgTerms_to_ttTerms([ccg(Id, CCGTerm_final)], [TTterm_ID]),
		TTterm_ID = tt_id(Id, TTterm),
		nl, write(Id), %write(' TTterms,'),
		latex_ttTerm_print_tree(S, 6,  TTterm_ID),
		%greason([TTterm], []);
		% normalization of TTterm
		ttTerm_to_norm_term(TTterm, Normal_Term, _Sig, _Lexicon, _),
		writeln(' yes'),
		latex_norm_term_print(S, Normal_Term)%,
		% reasoning 
		%assert_list(Sig, clean),
		%gvalid(Normal_Term ===> '*'),
		%write(' reasoning, YES')
		;
		% OTHERWISE
		nl, write(Id), 
		writeln(' No')
	).



latex_norm_term_print(S, Normal_Term) :-
	lambdaTerm_to_latex(Normal_Term, Latex_Term),
	write(S, Latex_Term),
	write(S, '\\\\').




