%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Description: Prolog CCG Tree in Latex
%     Version: 
%      Author: lasha.abzianidze{at}gmail.com 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- module(latex_ccgtree, 
	[
		ccgTree_to_tikzpicture/2
	]).
	
:- use_module('latex_ttterm', [latex_term/2]).	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Converts Prolog CCG tree in Tikzpicture
ccgTree_to_tikzpicture(S, CCGTree) :-
	%write(S, '  \\begin{scaletikzpicturetowidth}{\\textwidth}\n'),	% old
	%write(S, '  \\begin{tikzpicture}[scale=\\tikzscale, baseline=0pt, grow=down]\n'), % old
	write(S, '  \\noindent\\maxsize{\\begin{tikzpicture}[grow=down]\n'), % new
    write(S, '    \\tikzset{level distance = 25pt, sibling distance = 0pt}\n'),
	write(S, '    \\tikzset{every tree node/.style={align=center,anchor=north}}\n'),
    write(S, '    \\Tree\n'),
	once(ccgTree_to_latex(S, 6, CCGTree)),
	write(S, '  \\end{tikzpicture}\n'),
	%write(S, '  \\end{scaletikzpicturetowidth}\n'),	% old
	write(S, '  }\n'), 
	write(S, '  \\clearpage\n').


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% prints Prolog CCG tree in latex tree for Tikzpicture
ccgTree_to_latex(S, Pos, CCGTree) :-
	CCGTree = lx(Cat, OldCat, Tree_1), !,
	cat_to_latex(Cat, CatAt),
	cat_to_latex(OldCat, OldCatAt),
	Pos2 is Pos + 1, 
	tab(S, Pos),
	atomic_list_concat(['[.\\node{${\\tt lx}[', CatAt, ', ', OldCatAt, ']$};\n'], Latex),
	write(S, Latex),
	ccgTree_to_latex(S, Pos2, Tree_1),
	tab(S, Pos),
	write(S, ']\n').

ccgTree_to_latex(S, Pos, CCGTree) :-
	CCGTree = conj(Cat, OldCat, Conj_Tree, Tree_1), !,
	cat_to_latex(Cat, CatAt),
	cat_to_latex(OldCat, OldCatAt),
	Pos2 is Pos + 1, 
	tab(S, Pos),
	atomic_list_concat(['[.\\node{${\\tt conj}[', CatAt, ', ', OldCatAt, ']$};\n'], Latex),
	write(S, Latex),
	ccgTree_to_latex(S, Pos2, Conj_Tree),
	ccgTree_to_latex(S, Pos2, Tree_1),

	tab(S, Pos),
	write(S, ']\n').

ccgTree_to_latex(S, Pos, CCGTree) :-
	( CCGTree = tr(Cat, Tree_1)
	; CCGTree = tr(Cat, _, Tree_1) % for easyCCG
	),	!,
	cat_to_latex(Cat, CatAt),
	Pos2 is Pos + 1, 
	tab(S, Pos),
	atomic_list_concat(['[.\\node{${\\tt tr}[', CatAt, ']$};\n' ], Latex),
	write(S, Latex),
	ccgTree_to_latex(S, Pos2, Tree_1),
	tab(S, Pos),
	write(S, ']\n').

ccgTree_to_latex(S, Pos, CCGTree) :-
	CCGTree = t(Cat, Token, Lem, PosTag, Feat1, Feat2), !,
	cat_to_latex(Cat, CatAt),
	latex_term(Token, Latex_Token),
	latex_term(Lem, Latex_Lem),
	latex_term(PosTag, Latex_PosTag),
	tab(S, Pos),
	write(S, '[.\\node{\n'),
	tab(S, Pos),
	atomic_list_concat(['\\texttt{', Latex_Token, '}\\\\\n'], Print_Token),
	write(S, Print_Token),
	tab(S, Pos),
	atomic_list_concat(['$', CatAt, '$\\\\\n'], Print_Cat),
	write(S, Print_Cat),
	tab(S, Pos),
	atomic_list_concat(['\\textbf{', Latex_Lem, '}\\\\\n'], Print_Lem),
	write(S, Print_Lem),
	tab(S, Pos),
	atomic_list_concat(['\\normalsize{', Latex_PosTag, '}\\\\\n'], Print_PosTag),
	write(S, Print_PosTag),
	tab(S, Pos),
	atomic_list_concat(['\\scriptsize{', Feat1, '}\\\\\n'], Print_Feat1),
	write(S, Print_Feat1),
	tab(S, Pos),
	atomic_list_concat(['\\scriptsize{', Feat2, '}'], Print_Feat2),
	write(S, Print_Feat2),
	write(S, ' };\n'),
	tab(S, Pos),
	write(S, ']\n').

ccgTree_to_latex(S, Pos, CCGTree) :-
	CCGTree =.. [Funct, Cat, _, Tree_1, Tree_2 | _],
	once(member(Funct, [gbxc, gfxc, gfc, gbc])), !,
	Pos2 is Pos + 1,
	tab(S, Pos),
	cat_to_latex(Cat, CatAt),
	atomic_list_concat(['[.\\node{${\\tt ', Funct, '}[', CatAt, ']$};\n'], Latex),
	write(S, Latex),
	ccgTree_to_latex(S, Pos2, Tree_1),
	ccgTree_to_latex(S, Pos2, Tree_2),
	tab(S, Pos),
	write(S, ']\n').

ccgTree_to_latex(S, Pos, CCGTree) :-
	CCGTree =.. [Funct, Cat, Tree_1, Tree_2 | _],
	once(member(Funct, [fa, ba, fc, bc, fxc, bxc, rp, lp, rtc, ltc])), !,
	cat_to_latex(Cat, CatAt),
	Pos2 is Pos + 1,
	tab(S, Pos),	
	atomic_list_concat(['[.\\node{${\\tt ', Funct, '}[', CatAt, ']$};\n'], Latex),
	write(S, Latex),
	ccgTree_to_latex(S, Pos2, Tree_1),
	ccgTree_to_latex(S, Pos2, Tree_2),
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






