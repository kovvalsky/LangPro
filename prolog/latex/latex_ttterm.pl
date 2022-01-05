%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%   LaTeX Output for trees, Terms & LLFs
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- module(latex_ttterm,
	[
		latex_ttTerm_preambule/1,
		latex_ttTerm_print_tree/2,
		lambdaTerm_to_latex/2,
		latex_senIDs_trees/1,
		latex_senIDs_trees/2,
		latex_term/2,
		latex_probIDs_trees/1,
		latex_probIDs_trees/2,
		latex_senID_all_ders/2
	]).

:- use_module('latex_ccgtree', [ccgTree_to_tikzpicture/1, write_tikzpicture_begin/2,
	write_tikzpicture_end/0, ccgTree_to_latex/3]).
:- use_module('../printer/extract', [print_used_lexical_rules/2]).
:- use_module('../utils/user_preds',
	[probIDs_to_senIDs/2, listInt_to_id_ccgs/2, ttExp_to_ttTerm/2, sen_id2all_anno/2]
	).
:- use_module('../printer/reporting', [report/1]).
:- use_module('../llf/recognize_MWE', [clean_ccgTerm_once/2]).
:- use_module('../llf/ccg_term', [ccgIDTree_to_ccgIDTerm/2]).
:- use_module('../llf/ccgTerm_to_ttTerm', [ccgTerms_to_ttTerms/2]).
:- use_module('../llf/correct_term', [correct_ccgTerm/2]).
:- use_module('../llf/gen_quant', [once_gen_quant_tt/2]).
:- use_module('../utils/generic_preds', [filepath_write_source/2,
	format_list_list/3]).
:- use_module('../llf/ner', [ne_ccg/2]).
:- use_module('../llf/ttterm_to_term', [ttTerm_to_prettyTerm/2, ttTerm_to_norm_term/5]).
:- use_module('../lambda/lambda_tt', [op(605, yfx, @), op(605, xfy, ~>)]).
:- use_module(library(clpfd)). % for transpose/2

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Print CCG trees, CCG terms and LLFS
% of the list of RTE problems into a Latex file
latex_probIDs_trees(Prob_IDs) :-
	latex_probIDs_trees(Prob_IDs, 'RTE_to_LLF').

latex_probIDs_trees(Prob_IDs, LaTeXFile) :-
	filepath_write_source(LaTeXFile, S),
	latex_ttTerm_preambule(S),
	maplist(latex_probID_trees(S), Prob_IDs), !,
	write(S, '\\end{document}'),
	close(S).

% write info about the sentence with SID in S in Latex format
latex_probID_trees(LaTeXFile, PID) :-
	( is_stream(LaTeXFile) -> S = LaTeXFile
	; filepath_write_source(LaTeXFile, S) ),
	once(sen_id(_,PID,_,_,Lab,_)),
	findall([SID,PH,Raw], sen_id(SID,PID,PH,_,_,Raw), Info),
	format(S, '\\noindent\\texttt{[~w]} \\Large{\\textbf{~w}}~n~n', [PID, Lab]),
	format(atom(F), '\\noindent(~~w):[~w]~~w \\Large{\\textbf{~~w}}~n~n ', [PID]),
	format_list_list(S, F, Info), format(S, '~n~n', []), flush_output(S),
	% get CCG terms and TTterms for each sentence (inc. cross normalizations)
	probID_to_trees_terms(PID, SIDs, CCGTrees, TTs_L, Info_L),
	with_output_to(S, maplist(latex_senID_all_trees_terms(Info_L),
							  SIDs, CCGTrees, TTs_L) ).

% auxiliary predicates for printing problesm in latex
latex_senID_all_trees_terms(Info_L, SID, CCGTree, TTs) :-
	sen_id_latex(SID, 'CCGTree'),
	sen_id2all_anno(SID, Anno),
	write_tikzpicture_begin(50, 0),
	ccgTree_to_latex(Anno, 6, CCGTree),
	write_tikzpicture_end,
	maplist(latex_senID_ttterm(SID), TTs, Info_L).

latex_senID_ttterm(SID, TT, Info) :-
	sen_id_latex(SID, Info),
	latex_ttTerm_print_tree(6, TT).

probID_to_trees_terms(PID, SIDs, CCGTrees, TTs_L, Info_L) :-
	findall(SID, sen_id(SID,PID,_,_,_,_), SIDs),
	maplist(sen_id_to_ccgtree_base_ttterm, SIDs, CCGTrees, CCGTms),
	lex_norm_ttterms('ccg_norm', CCGTms, NormCCGTms, _),
	maplist(correct_ttterm, NormCCGTms, CorrTTs),
	lex_norm_ttterms(llf_norm, CorrTTs, NormTTs, _),
	maplist(once_gen_quant_tt, NormTTs, LLFs),
	transpose([CCGTms, NormCCGTms, CorrTTs, NormTTs, LLFs], TTs_L),
	Info_L = ['CCGTerm','NormCCGTerm','CorrTT','NormTT','LLF'].

sen_id_to_ccgtree_base_ttterm(SID, Tree, TTterm) :-
	once(sen_id2anno(SID, Tree, DetAnno)),
	ccgIDTree_to_ccgIDTerm(ccg(SID,Tree), ccg(SID,TTterm), DetAnno).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
latex_senID_all_ders(SID, LaTeXFile) :-
	filepath_write_source(LaTeXFile, S),
	latex_ttTerm_preambule(S),
	with_output_to(S, sen_id_latex(SID)),
	findall(Parser, (
		ccg(SID, Parser, CCGTree),
		format(S, '~n~n\\huge{~w}~n~n', [Parser]),
		with_output_to(S, write_tikzpicture_begin(50, 0)),
		sen_id2all_anno(SID, Anno),
		with_output_to(S, ccgTree_to_latex(Anno, 6, CCGTree)),
		with_output_to(S, write_tikzpicture_end)
	), _Ps),
	write(S, '\\end{document}'),
	close(S).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Given SenIDs, write corresponding CCG trees,
% CCG terms and LLFs in a Latex file
latex_senIDs_trees(List_Int) :-
	latex_senIDs_trees(List_Int, 'CCG_to_LLF').

latex_senIDs_trees(List_Int, LaTeXFile) :-
	listInt_to_id_ccgs(List_Int, CCG_IDs),
	filepath_write_source(LaTeXFile, S),
	% ( exists_directory('latex') -> true; make_directory('latex') ),
	% atomic_list_concat(['latex/', LaTeXFile, '.tex'], FilePath),
	% open(FilePath, write, S, [encoding(utf8), close_on_abort(true)]),
	%asserta(latex_file_stream(S)),
	latex_ttTerm_preambule(S),
	%retractall(event_index), % temporarily here
	%maplist(ccg_to_lambda_term_latex(S), CCG_IDs, TTterm_IDs), % for ttterms solution 1
	maplist(latex_senID_trees(S), CCG_IDs),
	!,
	write(S, '\\end{document}'),
	close(S).
	% findall(ccg(Id, TTterm), (member(ccg(Id, TTterm), TTterm_IDs), nonvar(TTterm)), WF_TTterms),
	% length(WF_TTterms, Num),
	% %findall(XX, member(ccg(XX, _), WF_TTterms), Output), write(Output),
	% length(TTterm_IDs, Total),
	% format(atom(Per), '~2f', [Num * 100 / Total]),
	% atomic_list_concat([Per, '% (', Num, ' from ', Total, ') of LLFs were generated\n'], Message),
	% write(Message).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% writes a CCG tree, a CCG term, a corrected CCG term
% and LLF(s) in a stream and returns LLF(s)_ID
latex_senID_trees(S, Id) :-
	( Id = ccg(SID,_) -> true; number(Id), SID = Id ),
	( debMode('pr_sen') -> sen_id(SID,_,_,_,Sen), report([SID,': ',Sen]); true ),
	report([SID]),
	% print sentence and CCGtree
	with_output_to(S, sen_id_latex(SID)),
	with_output_to(S, ccgTree_to_tikzpicture(SID)), 				% print
	% CCGtree to ccgTerm
	ccgIDTree_to_ccgIDTerm(SID, ccg(SID, CCGTerm)),
	with_output_to(S, latex_ttTerm_print_tree(2, CCGTerm)), 			% print
	%ne_ccg(CCGTerm, CCGTerm_1),
	%latex_ttTerm_print_tree(S, 6, CCGTerm_1), 			% print
	%clean_ccgTerm_once(CCGTerm_1, CCGTerm_2),
	%latex_ttTerm_print_tree(S, 6, CCGTerm_2),			% print
	CCGTerm_final = CCGTerm,
	correct_ccgTerm(CCGTerm_final, Corr_CCGTerm_final),
	print_used_lexical_rules(SID, Corr_CCGTerm_final),	% print
	with_output_to(S, latex_ttTerm_print_tree(2, Corr_CCGTerm_final)),	% print
	%% gen_quant_tt(Corr_CCGTerm_final, GQTTs),			% sick-train 7618 loops here
	%% maplist( latex_ttTerm_print_tree(S, 2), GQTTs ),	% print all GQ versions
	%% GQTTs = [GQTT|_],
	%% maplist( ttTerm_to_latexTerm, GQTTs, LatexTerms), maplist( writeln(S), LatexTerms).
	once_gen_quant_tt(Corr_CCGTerm_final, GQTT),
	ttTerm_to_latexTerm(GQTT, LatexTerm), writeln(S, LatexTerm), writeln(S, '\n'), % pronts first LLF as a term
	with_output_to(S, latex_ttTerm_print_tree(6, GQTT)).				% print the first GQ version


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
sen_id_latex(Id) :-
	sen_id_latex(Id, '').

sen_id_latex(Id, Info) :-
	once( (sen_id(Id,_,_,_,Sen); sen_id(Id,_,_,_,_,Sen)) ),
	(Info = '' -> Delim = ''; Delim = ':'),
	format('  \\texttt{~w:} \\textbf{~w}\\texttt{~w ~w}~n~n', [Id, Info, Delim, Sen]).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% prints latex preambule for ttTerms
latex_ttTerm_preambule(S) :-
	write(S, '\\documentclass[landscape]{article}\n'),
	write(S, '\\setlength\\textwidth{10in}\n'),
	write(S, '\\setlength\\textheight{8.5in}\n'),
	write(S, '\\setlength\\oddsidemargin{-.5in}\n'),
	write(S, '\\setlength\\evensidemargin{-.5in}\n'),
	write(S, '\\setlength\\topmargin{-.7in}\n'),
	write(S, '\\setlength\\headsep{0in}\n'),
	write(S, '\\setlength\\headheight{0in}\n'),
	write(S, '\\setlength\\topskip{0in}\n'),
	write(S, '\\usepackage[utf8]{inputenc}\n'),
	write(S, '\\usepackage{tikz-qtree-compat}\n'),
	write(S, '%\\usepackage{spverbatim}\n'),
	write(S, '\\usepackage{amssymb}\n'),
	write(S, '\\usepackage{rotating}\n'),
	write(S, '\\usepackage{color}\n'),
	write(S, '%\\usepackage{environ}\n'),
	write(S, '\\usepackage{graphicx}\n'), 	% new
	write(S, '\\usepackage{calc}\n'), 		% new
/*	write(S, '\\makeatletter\n'),
	write(S, '\\newsavebox{\\measure@tikzpicture}\n'),
	write(S, '\\NewEnviron{scaletikzpicturetowidth}[1]{%\n'),
  	write(S, '  \\def\\tikz@width{#1}%\n'),
  	write(S, '  \\def\\tikzscale{1}\\begin{lrbox}{\\measure@tikzpicture}%\n'),
  	write(S, '  \\BODY\n'),
  	write(S, '  \\end{lrbox}%\n'),
  	write(S, '  \\pgfmathparse{#1/\\wd\\measure@tikzpicture}%\n'),
  	write(S, '  \\edef\\tikzscale{\\pgfmathresult}%\n'),
  	write(S, '  \\BODY\n'),
	write(S, '}\n'),
	write(S, '\\makeatother\n'). % old format */
	write(S, '\n\\newlength{\\xsize}\n\\newlength{\\ysize}\n\\newsavebox{\\tempbox}\n\n'),
	write(S, '\\newcommand{\\maxsize}[1]{\n  \\savebox{\\tempbox}{#1}\n  \\settoheight{\\ysize}{\\usebox{\\tempbox}}\n'),
	write(S, '  \\settowidth{\\xsize}{\\usebox{\\tempbox}}\n  \\pgfmathparse{\\xsize/\\textwidth > \\ysize/\\textheight}\n'),
	write(S, '  \\if \\pgfmathresult1\n    \\resizebox{\\textwidth}{!}{\\usebox{\\tempbox}}\n  \\else\n'),
	write(S, '    \\resizebox{!}{\\textheight-2cm}{\\usebox{\\tempbox}}\n  \\fi\n}\n\n'),
	write(S, '\\begin{document}\n').




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% prints complete ttTerm in latex tikzpicture fashion
latex_ttTerm_print_tree(Pos, TTterm) :-
	write_tikzpicture_begin(25, -5),
	latex_ttTerm_print(Pos, TTterm),
	write_tikzpicture_end.



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% prints ttTerm in latex tree fashion
latex_ttTerm_print(Pos, TTterm) :-
	TTterm = (SubTTterm, Type),
	nonvar(SubTTterm),
	SubTTterm = TTterm1 @ TTterm2,
	!,
	tab(Pos),
	latex_type(Type, Latex_type),
	atomic_list_concat(['[.\\node{$', Latex_type, '$};'], Node),
	writeln(Node),
	Pos2 is Pos + 1,
	%write('intermediate none Sibl1: '), write(TTterm1), write('\n'),
	%write('intermediate none Sibl2: '), write(TTterm2), write('\n'),
	latex_ttTerm_print(Pos2, TTterm1),
	%write('intermediate one Sibl1: '), write(TTterm1), write('\n'),
	%write('intermediate notyet 2nd Sibl2: '), write(TTterm2), write('\n'),
	latex_ttTerm_print(Pos2, TTterm2),
	%write('intermediate both Sibl1: '), write(TTterm1), write('\n'),
	%write('intermediate both Sibl2: '), write(TTterm2), write('\n'),
	tab(Pos),
	writeln(']').

latex_ttTerm_print(Pos, TTterm) :-
	TTterm = (SubTTterm, Type),
	nonvar(SubTTterm),
	SubTTterm = abst(X, TTterm1),
	!,
	tab(Pos),
	latex_type(Type, Latex_type),
	atomic_list_concat(['[.\\node{$', Latex_type, '$};'], Node),
	writeln(Node),
	Pos2 is Pos + 1,
	%write('intermediate none Abst: '), write(abst(X)), write('\n'),
	%write('intermediate none Body: '), write(TTterm1), write('\n'),
	latex_ttTerm_print(Pos2, abst(X)),
	%write('intermediate one Abst: '), write(abst(X)), write('\n'),
	%write('intermediate notyet Body: '), write(TTterm1), write('\n'),
	latex_ttTerm_print(Pos2, TTterm1),
	%write('intermediate both Abst: '), write(abst(X)), write('\n'),
	%write('intermediate both Body: '), write(TTterm1), write('\n'),
	tab(Pos),
	writeln(']').

latex_ttTerm_print(Pos, TTterm) :-
	nonvar(TTterm),
	TTterm = (TT, Type),
	nonvar(TT),
	TT = (_,_),
	!,
	tab(Pos),
	latex_type(Type, Latex_type),
	atomic_list_concat(['[.\\node{$', Latex_type, '$};'], Node),
	writeln(Node),
	Pos2 is Pos + 1,
	latex_ttTerm_print(Pos2, TT),
	tab(Pos),
	writeln(']').

latex_ttTerm_print(Pos, TTterm) :-
	nonvar(TTterm),
	TTterm = (Term, Type),
	nonvar(Term),
	( Term = tlp(Token, Lem, PosTag, _, NE)
	; Term = tlp(Token, Lem, PosTag), NE = ' '),
	!,
	latex_term(Token, Latex_Token),
	latex_term(Lem, Latex_Lem),
	latex_term(PosTag, Latex_PosTag),
	tab(Pos),
	latex_type(Type, Latex_type),
	Pos8 is Pos,% + 8,
	( NE == 'Ins' ->
		write('[.\\node[text=green]{\n');
	  Type = np:_ ->
		write('[.\\node[text=red]{\n');
	  write('[.\\node{\n') ),
	tab(Pos8),
	format('\\scriptsize{~w}\\\\\n', [Latex_Token]),
	tab(Pos8),
	format('$~w$\\\\\n', [Latex_type]),
	tab(Pos8),
	format('\\textbf{~w}\\\\\n', [Latex_Lem]),
	tab(Pos8),
	format('\\normalsize{~w}\\\\\n', [Latex_PosTag]),
	% tab(S, Pos8),
	% format(S, '\\scriptsize{~w}\\\\\n', [Feat1]),
	tab(Pos8),
	format('\\scriptsize{~w} };\n', [NE]),
	tab(Pos8),
	writeln(']').

latex_ttTerm_print(Pos, TTterm) :-
	nonvar(TTterm),
	TTterm = (Term, Type),
	!,
	latex_term(Term, Latex_term),
	%write('Atom: '), writeln(Latex_term),
	latex_type(Type, Latex_type),
	tab(Pos),
	write('[.\\node{'),
	Pos3 is Pos + 3,
	Pos5 is Pos + 5,
	%Pos7 is Pos + 7,
	tab(Pos5),
	write('\\textbf{'),
	write(Latex_term),
	write('}\\\\\n'),
	tab(Pos5),
	%write(S, '\\begin{sideways}\n'),
	%tab(S, Pos7),
	write('$'),
	write(Latex_type),
	write('$\n'),
	%tab(S, Pos5),
	%write(S, '\\end{sideways}\n'),
	tab(Pos3),
	write(' };\n'),
	tab(Pos),
	writeln(']').

latex_ttTerm_print(Pos, VarTerm) :-
	latex_term(VarTerm, Latex_term),
	VarTerm = abst((_Var, Type)),
	latex_type(Type, Latex_type),
	tab(Pos),
	write('[.\\node{'),
	Pos3 is Pos + 3,
	Pos5 is Pos + 5,
	tab(Pos5),
	write('\\textbf{'),
	write(Latex_term),
	write('}\\\\\n'),
	tab(Pos5),
	write('$'),
	write(Latex_type),
	write('$\n'),
	tab(Pos3),
	write(' };\n'),
	tab(Pos),
	writeln(']').


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% convert type according to latex syntax
latex_type(Type, Latex_type) :-
	var(Type), !,
	term_to_atom(Type, Atom_type),
	atom_to_chars(Atom_type, [_, _ | Index_List]),
	atom_to_chars(Index, Index_List),
	atomic_list_concat(['TY_{', Index, '}'], Latex_type).

latex_type(A, A) :-
	atom(A), !.

latex_type(A ~> B, Latex_type) :-
	!, latex_type(A, Latex_A),
	latex_type(B, Latex_B),
	( nonvar(A), A = _Ty1~>_Ty2 ->
		atomic_list_concat(['(', Latex_A, '),', Latex_B], Latex_type);
	    atomic_list_concat([Latex_A, ',', Latex_B], Latex_type)).

latex_type(Type:Feat, Latex_type) :-
	latex_type(Type, Latex_ty),
	(var(Feat) ->
		Latex_type = Latex_ty;
		atomic_list_concat([Latex_ty, '_{', Feat, '}'], Latex_type) ).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% convert term according to latex syntax
latex_term(Term, Latex_term) :-
	var(Term) ->
		term_to_atom(Term, Atom_term),
		atom_to_chars(Atom_term, [_, _ | Index_List]),
		atom_to_chars(Index, Index_List),
		%write('Printing: '), write(Atom_term), write('\n'), write(Index), write('\n'),
		atomic_list_concat(['$X_{', Index, '}$'], Latex_term);
	Term = abst((Var, _)) ->
		term_to_atom(Var, Atom_term),
		atom_to_chars(Atom_term, [_, _ | Index_List]),
		atom_to_chars(Index, Index_List),
		%write('Printing: '), write(Atom_term), write('\n'), write(Index), write('\n'),
		atomic_list_concat(['$\\lambda X_{', Index, '}$'], Latex_term);
	is_list(Term) ->
		maplist([A,B]>>term_to_atom(A,B), Term, AtTms),
		atomic_list_concat(AtTms, '; ', Latex_term);
	atom_to_latex(Term, Latex_term).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
atom_to_latex(A, L) :-
	atomic(A),
	atomic_list_concat(List1, '&', A),
	atomic_list_concat(List1, '\\&', A1),
	atomic_list_concat(List2, '_', A1),
	atomic_list_concat(List2, '\\_', A2),
	atomic_list_concat(List3, '$', A2),
	atomic_list_concat(List3, '\\$', A3),
	atomic_list_concat(List4, '%', A3),
	atomic_list_concat(List4, '\\%', A4),
	atomic_list_concat(List5, '#', A4),
	atomic_list_concat(List5, '\\#', L).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% convert lambda term according to latex syntax
lambdaTerm_to_latex(Term, Latex_term) :-
	var(Term),
	!,
	term_to_atom(Term, Atom_term),
	atom_to_chars(Atom_term, [_, _ | Index_List]),
	atom_to_chars(Index, Index_List),
	atomic_list_concat(['$X_{', Index, '}$'], Latex_term).

lambdaTerm_to_latex(Term1 @ Term2, Latex_term) :-
	!,
	lambdaTerm_to_latex(Term1, Latex1),
	lambdaTerm_to_latex(Term2, Latex2),
	((nonvar(Term2), Term2 = _ @ _) ->
		atomic_list_concat([Latex1, ' (', Latex2, ')'], Latex_term);
	atomic_list_concat([Latex1, ' ', Latex2], Latex_term)).

lambdaTerm_to_latex(abst(X, Term), Latex_term) :-
	!,
	term_to_atom(X, Atom_term),
	atom_to_chars(Atom_term, [_, _ | Index_List]),
	atom_to_chars(Index, Index_List),
	lambdaTerm_to_latex(Term, Latex),
	atomic_list_concat(['$(\\lambda X_{', Index, '}$.', Latex, ')'], Latex_term).

lambdaTerm_to_latex(Term, Latex_term) :-
	Term == '$' ->
		Latex_term = '\\$';
	Term == '%' ->
		Latex_term = '\\%';
	Term == '#' ->
		Latex_term = '\\#';
	atomic_list_concat(Parts1, '&', Term),
	atomic_list_concat(Parts1, '\\&', Temp1),
	atomic_list_concat(Parts2, '_', Temp1),
	atomic_list_concat(Parts2, '\\_', Temp2),
	atomic_list_concat(Parts3, '$', Temp2),
	atomic_list_concat(Parts3, '\\$', Latex_term).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% TTterm to latex term
ttTerm_to_latexTerm(TT, LatexTerm) :-
	ttExp_to_ttTerm(TT, TTterm), % just for asistance
	ttTerm_to_prettyTerm(TTterm, PrettyTerm),
	lambdaTerm_to_latex(PrettyTerm, LatexTerm).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ccg_to_lambda_term_latex(S, ID_CCG, TTterm_ID)
% converst ID_CCG pair into CCGTerm, CCGTerm into ttTerms (may fail),
% then prints target sentence, ID_CCG, CCGterm, ttTerms in latex way on S chanelle
ccg_to_lambda_term_latex(ID_CCG, TTterm_ID) :-
	ID_CCG = ccg(Id, _CCGTree),
	% print sentence and CCGtree
	sen_id_latex(Id),
	ccgTree_to_tikzpicture(Id),
	% CCGtree to ccgTerm
	ccgIDTree_to_ccgIDTerm(ID_CCG, ccg(Id, CCGTerm)),
	ne_ccg(CCGTerm, CCGTerm_1),
	clean_ccgTerm_once(CCGTerm_1, CCGTerm_2),
	CCGTerm_final = CCGTerm_2,
	% print ccgTerm
	latex_ttTerm_print_tree(6, CCGTerm_final),
	%ignore(ccgTerms_to_ttTerms([CCG_ID_term_final], [TTterm_ID])),
	(	%getting TTterm
		ccgTerms_to_ttTerms([ccg(Id, CCGTerm_final)], [TTterm_ID]),
		TTterm_ID = tt_id(Id, TTterm),
		nl, write(Id), %write(' TTterms,'),
		latex_ttTerm_print_tree(6,  TTterm_ID),
		%greason([TTterm], []);
		% normalization of TTterm
		ttTerm_to_norm_term(TTterm, Normal_Term, _Sig, _Lexicon, _),
		writeln(' yes'),
		latex_norm_term_print(Normal_Term)%,
		% reasoning
		%assert_list(Sig, clean),
		%gvalid(Normal_Term ===> '*'),
		%write(' reasoning, YES')
		;
		% OTHERWISE
		nl, write(Id),
		writeln(' No')
	).

latex_norm_term_print(Normal_Term) :-
	lambdaTerm_to_latex(Normal_Term, Latex_Term),
	write(Latex_Term),
	write('\\\\').
