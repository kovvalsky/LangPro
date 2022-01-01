%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Description: Prolog CCG Tree in Latex
%     Version:
%      Author: lasha.abzianidze{at}gmail.com
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- module(latex_ccgtree,
	[
		ccgTree_to_tikzpicture/2,
		write_tikzpicture_begin/2,
		write_tikzpicture_end/0,
		ccgTree_to_latex/4
	]).

:- use_module('latex_ttterm', [latex_term/2]).
:- use_module('../utils/user_preds', [off2anno/3, sen_id2anno/3]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Converts Prolog CCG tree in Tikzpicture
ccgTree_to_tikzpicture(S, SID) :-
	with_output_to(S, write_tikzpicture_begin(25, 0)),
	( number(SID) -> sen_id2anno(SID, CCGTree, Anno) % t/3 format with ID input
	; SID = ccg(ID, CCGTree), sen_id2anno(ID, CCGTree, Anno) ), % t/3 format with ID ccg/2 input
	once(ccgTree_to_latex(S, Anno, 6, CCGTree)),
	with_output_to(S, write_tikzpicture_end).

% Latex related wrapper for tikzpicture
write_tikzpicture_begin(Level, Sibling) :-
	format('  \\noindent\\maxsize{\\begin{tikzpicture}[grow=down]\n', []),
	format('    \\tikzset{level distance = ~wpt, sibling distance = ~wpt}\n', [Level, Sibling]),
	format('    \\tikzset{every tree node/.style={align=center,anchor=north}}\n    \\Tree\n', []).

write_tikzpicture_end :-
	format('  \\end{tikzpicture}\n  }\n  \\clearpage\n', []).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% prints Prolog CCG tree in latex tree for Tikzpicture
% accomodates both a new offset style and old-style t/5
ccgTree_to_latex(S, Anno, Pos, CCGTree) :-
	( CCGTree = t(Cat, Token, Offset) ->
		off2anno(Anno, [Offset], A),
		(Token, Lem, PosTag, NE) = (A.t, A.l, A.ppos, A.ner)
	; CCGTree = t(Cat, Token, Lem, PosTag, _I, NE) ), !,
	cat_to_latex(Cat, CatAt),
	latex_term(Token, Latex_Token),
	latex_term(Lem, Latex_Lem),
	latex_term(PosTag, Latex_PosTag),
	with_output_to(atom(Indent), tab(Pos)),
	format(S, '~w[.\\node{~n', [Indent]),
	format(S, '~w\\texttt{~w}\\\\~n', [Indent, Latex_Token]),
	format(S, '~w$~w$\\\\~n', [Indent, CatAt]),
	format(S, '~w\\textbf{~w}\\\\~n', [Indent, Latex_Lem]),
	format(S, '~w\\normalsize{~w}\\\\~n', [Indent, Latex_PosTag]),
%	format(S, '~w\\scriptsize{~w}\\\\~n', [Indent, I]),
	format(S, '~w\\scriptsize{~w}\\\\~n', [Indent, NE]),
	format(S, ' };~n~w]~n', [Indent]).


ccgTree_to_latex(S, Anno,  Pos, CCGTree) :-
	( CCGTree = lex(Cat, OldCat, Tree_1)
	; CCGTree = lx(Cat, OldCat, Tree_1) ), !,
	cat_to_latex(Cat, CatAt),
	cat_to_latex(OldCat, OldCatAt),
	Pos2 is Pos + 1,
	tab(S, Pos),
	atomic_list_concat(['[.\\node{${\\tt lx}[', CatAt, ', ', OldCatAt, ']$};\n'], Latex),
	write(S, Latex),
	ccgTree_to_latex(S, Anno, Pos2, Tree_1),
	tab(S, Pos),
	write(S, ']\n').

ccgTree_to_latex(S, Anno, Pos, CCGTree) :-
	CCGTree = conj(Cat, OldCat, Conj_Tree, Tree_1), !,
	cat_to_latex(Cat, CatAt),
	cat_to_latex(OldCat, OldCatAt),
	Pos2 is Pos + 1,
	tab(S, Pos),
	atomic_list_concat(['[.\\node{${\\tt conj}[', CatAt, ', ', OldCatAt, ']$};\n'], Latex),
	write(S, Latex),
	ccgTree_to_latex(S, Anno, Pos2, Conj_Tree),
	ccgTree_to_latex(S, Anno, Pos2, Tree_1),
	tab(S, Pos),
	write(S, ']\n').

ccgTree_to_latex(S, Anno, Pos, CCGTree) :-
	( CCGTree = tr(Cat, Tree_1)
	; CCGTree = tr(Cat, _, Tree_1) % for easyCCG
	),	!,
	cat_to_latex(Cat, CatAt),
	Pos2 is Pos + 1,
	tab(S, Pos),
	atomic_list_concat(['[.\\node{${\\tt tr}[', CatAt, ']$};\n' ], Latex),
	write(S, Latex),
	ccgTree_to_latex(S, Anno, Pos2, Tree_1),
	tab(S, Pos),
	write(S, ']\n').

ccgTree_to_latex(S, Anno, Pos, CCGTree) :-
	CCGTree =.. [Funct, Cat, _, Tree_1, Tree_2 | _],
	memberchk(Funct, [gbxc, gfxc, gfc, gbc]), !,
	Pos2 is Pos + 1,
	tab(S, Pos),
	cat_to_latex(Cat, CatAt),
	atomic_list_concat(['[.\\node{${\\tt ', Funct, '}[', CatAt, ']$};\n'], Latex),
	write(S, Latex),
	ccgTree_to_latex(S, Anno, Pos2, Tree_1),
	ccgTree_to_latex(S, Anno, Pos2, Tree_2),
	tab(S, Pos),
	write(S, ']\n').

ccgTree_to_latex(S, Anno, Pos, CCGTree) :-
	CCGTree =.. [Funct, Cat, Tree_1, Tree_2 | _],
	memberchk(Funct, [fa, ba, fc, bc, fxc, bxc, fx, bx, rp, lp, rtc, ltc]), !,
	cat_to_latex(Cat, CatAt),
	Pos2 is Pos + 1,
	tab(S, Pos),
	atomic_list_concat(['[.\\node{${\\tt ', Funct, '}[', CatAt, ']$};\n'], Latex),
	write(S, Latex),
	ccgTree_to_latex(S, Anno, Pos2, Tree_1),
	ccgTree_to_latex(S, Anno, Pos2, Tree_2),
	tab(S, Pos),
	write(S, ']\n').



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% converts ccg syntax category in latex syntax
cat_to_latex(Cat, Latex) :-
	term_to_atom(Cat, CatAt),
	atomic_list_concat(List, '\\', CatAt),
	atomic_list_concat(List, '\\backslash ', CatAt_1),
	atomic_list_concat(List_1, ':', CatAt_1),
	atomic_list_concat(List_1, '\\!:\\!', Latex).
