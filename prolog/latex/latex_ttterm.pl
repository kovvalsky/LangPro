%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%   LaTeX Output for trees, Terms & LLFs
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- module(latex_ttterm,
	[
		latex_ttTerm_preambule/1,
		latex_ttTerm_print_tree/3,
		lambdaTerm_to_latex/2,
		latex_senIDs_trees/1,
		latex_senIDs_trees/2,
		latex_term/2,
		latex_probIDs_trees/1,
		latex_probIDs_trees/2,
		latex_senID_all_ders/2
	]).

:- use_module('latex_ccgtree', [ccgTree_to_tikzpicture/2, write_tikzpicture_begin/2,
	write_tikzpicture_end/0, ccgTree_to_latex/4]).
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
	findall([SID,PH,Raw],(
		sen_id(SID,PID,PH,_,_,Raw)
	), Info),
	format(S, '\\noindent\\texttt{[~w]} \\Large{\\textbf{~w}}~n~n', [PID, Lab]),
	format(atom(F), '\\noindent(~~w):[~w]~~w \\Large{\\textbf{~~w}}~n~n ', [PID]),
	format_list_list(S, F, Info),
	format(S, '~n~n', []),
	flush_output(S),
	maplist([[SID|_],SID]>>true, Info, SIDs),
	maplist(latex_senID_trees(S), SIDs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
latex_senID_all_ders(SID, LaTeXFile) :-
	filepath_write_source(LaTeXFile, S),
	latex_ttTerm_preambule(S),
	sen_id_latex(S, SID),
	findall(P, (
		ccg(SID, P, CCGTree),
		format(S, '~n~n\\huge{~w}~n~n', [P]),
		with_output_to(S, write_tikzpicture_begin(50, 0)),
		sen_id2all_anno(SID, Anno),
		ccgTree_to_latex(S, Anno, 6, CCGTree),
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
	sen_id_latex(S, SID),
	ccgTree_to_tikzpicture(S, SID), 				% print
	% CCGtree to ccgTerm
	ccgIDTree_to_ccgIDTerm(SID, ccg(SID, CCGTerm)),
	latex_ttTerm_print_tree(S, 2, CCGTerm), 			% print
	ne_ccg(CCGTerm, CCGTerm_1),
	%latex_ttTerm_print_tree(S, 6, CCGTerm_1), 			% print
	clean_ccgTerm_once(CCGTerm_1, CCGTerm_2),
	%latex_ttTerm_print_tree(S, 6, CCGTerm_2),			% print
	CCGTerm_final = CCGTerm_2,
	correct_ccgTerm(CCGTerm_final, Corr_CCGTerm_final),
	print_used_lexical_rules(SID, Corr_CCGTerm_final),	% print
	latex_ttTerm_print_tree(S, 2, Corr_CCGTerm_final),	% print
	%% gen_quant_tt(Corr_CCGTerm_final, GQTTs),			% sick-train 7618 loops here
	%% maplist( latex_ttTerm_print_tree(S, 2), GQTTs ),	% print all GQ versions
	%% GQTTs = [GQTT|_],
	%% maplist( ttTerm_to_latexTerm, GQTTs, LatexTerms), maplist( writeln(S), LatexTerms).
	once_gen_quant_tt(Corr_CCGTerm_final, GQTT),
	ttTerm_to_latexTerm(GQTT, LatexTerm), writeln(S, LatexTerm), writeln(S, '\n'), % pronts first LLF as a term
	latex_ttTerm_print_tree(S, 6, GQTT).				% print the first GQ version



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
sen_id_latex(S, Id) :-
	once( (sen_id(Id,_,_,_,Sen); sen_id(Id,_,_,_,_,Sen)) ),
	format(S, '  \\texttt{~w: ~w}~n~n', [Id, Sen]).



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
latex_ttTerm_print_tree(S, Pos, TTterm) :-
	with_output_to(S, write_tikzpicture_begin(25, -5)),
	latex_ttTerm_print(S, Pos, TTterm),
	with_output_to(S, write_tikzpicture_end).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% prints ttTerm in latex tree fashion
latex_ttTerm_print(S, Pos, TTterm) :-
	TTterm = (SubTTterm, Type),
	nonvar(SubTTterm),
	SubTTterm = TTterm1 @ TTterm2,
	!,
	tab(S, Pos),
	latex_type(Type, Latex_type),
	atomic_list_concat(['[.\\node{$', Latex_type, '$};'], Node),
	write(S, Node),
	nl(S),
	Pos2 is Pos + 1,
	%write('intermediate none Sibl1: '), write(TTterm1), write('\n'),
	%write('intermediate none Sibl2: '), write(TTterm2), write('\n'),
	latex_ttTerm_print(S, Pos2, TTterm1),
	%write('intermediate one Sibl1: '), write(TTterm1), write('\n'),
	%write('intermediate notyet 2nd Sibl2: '), write(TTterm2), write('\n'),
	latex_ttTerm_print(S, Pos2, TTterm2),
	%write('intermediate both Sibl1: '), write(TTterm1), write('\n'),
	%write('intermediate both Sibl2: '), write(TTterm2), write('\n'),
	tab(S, Pos),
	write(S, ']'), nl(S).

latex_ttTerm_print(S, Pos, TTterm) :-
	TTterm = (SubTTterm, Type),
	nonvar(SubTTterm),
	SubTTterm = abst(X, TTterm1),
	!,
	tab(S, Pos),
	latex_type(Type, Latex_type),
	atomic_list_concat(['[.\\node{$', Latex_type, '$};'], Node),
	write(S, Node),
	nl(S),
	Pos2 is Pos + 1,
	%write('intermediate none Abst: '), write(abst(X)), write('\n'),
	%write('intermediate none Body: '), write(TTterm1), write('\n'),
	latex_ttTerm_print(S, Pos2, abst(X)),
	%write('intermediate one Abst: '), write(abst(X)), write('\n'),
	%write('intermediate notyet Body: '), write(TTterm1), write('\n'),
	latex_ttTerm_print(S, Pos2, TTterm1),
	%write('intermediate both Abst: '), write(abst(X)), write('\n'),
	%write('intermediate both Body: '), write(TTterm1), write('\n'),
	tab(S, Pos),
	write(S, ']'), nl(S).

latex_ttTerm_print(S, Pos, TTterm) :-
	nonvar(TTterm),
	TTterm = (TT, Type),
	nonvar(TT),
	TT = (_,_),
	!,
	tab(S, Pos),
	latex_type(Type, Latex_type),
	atomic_list_concat(['[.\\node{$', Latex_type, '$};'], Node),
	write(S, Node),
	nl(S),
	Pos2 is Pos + 1,
	latex_ttTerm_print(S, Pos2, TT),
	tab(S, Pos),
	write(S, ']'), nl(S).

latex_ttTerm_print(S, Pos, TTterm) :-
	nonvar(TTterm),
	TTterm = (Term, Type),
	nonvar(Term),
	( Term = tlp(Token, Lem, PosTag, _, NE)
	; Term = tlp(Token, Lem, PosTag), NE = ' '),
	!,
	latex_term(Token, Latex_Token),
	latex_term(Lem, Latex_Lem),
	latex_term(PosTag, Latex_PosTag),
	tab(S, Pos),
	latex_type(Type, Latex_type),
	Pos8 is Pos,% + 8,
	( NE == 'Ins' ->
		write(S, '[.\\node[text=green]{\n');
	  Type = np:_ ->
		write(S, '[.\\node[text=red]{\n');
	  write(S, '[.\\node{\n') ),
	tab(S, Pos8),
	format(S, '\\scriptsize{~w}\\\\\n', [Latex_Token]),
	tab(S, Pos8),
	format(S, '$~w$\\\\\n', [Latex_type]),
	tab(S, Pos8),
	format(S, '\\textbf{~w}\\\\\n', [Latex_Lem]),
	tab(S, Pos8),
	format(S, '\\normalsize{~w}\\\\\n', [Latex_PosTag]),
	% tab(S, Pos8),
	% format(S, '\\scriptsize{~w}\\\\\n', [Feat1]),
	tab(S, Pos8),
	format(S, '\\scriptsize{~w} };\n', [NE]),
	tab(S, Pos8),
	write(S, ']\n').

latex_ttTerm_print(S, Pos, TTterm) :-
	nonvar(TTterm),
	TTterm = (Term, Type),
	!,
	latex_term(Term, Latex_term),
	%write('Atom: '), writeln(Latex_term),
	latex_type(Type, Latex_type),
	tab(S, Pos),
	write(S, '[.\\node{'),
	Pos3 is Pos + 3,
	Pos5 is Pos + 5,
	%Pos7 is Pos + 7,
	tab(S, Pos5),
	write(S, '\\textbf{'),
	write(S, Latex_term),
	write(S, '}\\\\\n'),
	tab(S, Pos5),
	%write(S, '\\begin{sideways}\n'),
	%tab(S, Pos7),
	write(S, '$'),
	write(S, Latex_type),
	write(S, '$\n'),
	%tab(S, Pos5),
	%write(S, '\\end{sideways}\n'),
	tab(S, Pos3),
	write(S, ' };\n'),
	tab(S, Pos),
	write(S, ']\n').

latex_ttTerm_print(S, Pos, VarTerm) :-
	latex_term(VarTerm, Latex_term),
	VarTerm = abst((_Var, Type)),
	latex_type(Type, Latex_type),
	tab(S, Pos),
	write(S, '[.\\node{'),
	Pos3 is Pos + 3,
	Pos5 is Pos + 5,
	tab(S, Pos5),
	write(S, '\\textbf{'),
	write(S, Latex_term),
	write(S, '}\\\\\n'),
	tab(S, Pos5),
	write(S, '$'),
	write(S, Latex_type),
	write(S, '$\n'),
	tab(S, Pos3),
	write(S, ' };\n'),
	tab(S, Pos),
	write(S, ']\n').


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
ccg_to_lambda_term_latex(S, ID_CCG, TTterm_ID) :-
	ID_CCG = ccg(Id, _CCGTree),
	% print sentence and CCGtree
	sen_id_latex(S, Id),
	ccgTree_to_tikzpicture(S, Id),
	% CCGtree to ccgTerm
	ccgIDTree_to_ccgIDTerm(ID_CCG, ccg(Id, CCGTerm)),
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
