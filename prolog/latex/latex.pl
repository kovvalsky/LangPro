%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Description: Creates Latex File of Tableau Proof
%     Version: 12.06.12
%      Author: lasha.abzianidze{at}gmail.com 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- module(latex, 
	[
		drawInLatex/1,
		tree_structure/1
	]).

:- use_module('../printer/reporting', [report/1]).
:- use_module('../lambda/lambda_tt', [op(605, yfx, @), op(605, xfy, ~>)]).
:- use_module('latex_ttterm', [lambdaTerm_to_latex/2]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% drawInLatex(Tree)
% Creates a latex file, writes preamble, 
% imports packages and writes beginings of Tree
:- dynamic tree_structure/1.
tree_structure(nil).
	
drawInLatex(Style) :-
	tree_structure(Tree),
	(exists_directory('latex') -> true; make_directory('latex')),
	open('latex/tree.tex', write, S, [encoding(utf8)]),
	% Latex code
	write(S, '\\documentclass{article}\n'),
	write(S, '\\usepackage{tikz-qtree-compat}\n\\usepackage{amssymb}\n\\usepackage{environ}\n\\usepackage{amsmath}\n'),
	( Style = 'forest' -> write(S, '\\usepackage{forest}\n'); true ),
	write(S, '\\makeatletter\n'),
	write(S, '\\newsavebox{\\measure@tikzpicture}\n'),
	write(S, '\\NewEnviron{scaletikzpicturetowidth}[1]{%\n'),
  	write(S, '  \\def\\tikz@width{#1}%\n'),
  	write(S, '  \\def\\tikzscale{1}\\begin{lrbox}{\\measure@tikzpicture}%\n'),
  	write(S, '  \\BODY\n'),
  	write(S, '  \\end{lrbox}%\n'),
  	write(S, '  \\pgfmathparse{#1/\\wd\\measure@tikzpicture}%\n'),
  	write(S, '  \\edef\\tikzscale{\\pgfmathresult}%\n'),
  	write(S, '  \\BODY\n'),
	write(S, '}\n\\makeatother\n'),
	write(S, '\\newcommand{\\lab}[1]{\\mybox[fill=gray!20]{#1}}\n'),
	write(S, '\\newcommand\\mybox[2][]{\\tikz[overlay]\\node[fill=blue!20,inner sep=2pt, anchor=text, rectangle, rounded corners=1mm,#1] {#2};\\phantom{#2}}\n'),
	write(S, '\\newcommand{\\T}{\\mathbb{T}}\n\\newcommand{\\F}{\\mathbb{F}}\n'),
	write(S, '\\newcommand{\\synt}[1]{\\textbf{\\small{#1}}}\n\\newcommand{\\semt}[1]{\\tt #1}\n'),
	write(S, '\\newcommand{\\btimes}{\\scalebox{1.5}{$\\times$}}\n\\newcommand{\\elist}{\\scalebox{.9}{[\\,]}}\n'),
	write(S, '\\newcommand{\\clrule}{$\\leq\\!$\\raisebox{-1pt}{\\scalebox{1}{$\\btimes$}}}\n'),
	write(S, '\\newcommand{\\pp}{{\\tt pp}}\n\\newcommand{\\np}{{\\tt np}}\n\\newcommand{\\sen}{{\\tt s}}\n\\newcommand{\\vp}{{\\tt vp}}\n\\newcommand{\\nou}{{\\tt n}}\n\\newcommand{\\qu}{{\\tt qu}}\n'),
	write(S, '\\newcommand{\\rulen}[1]{{\\normalfont\\textsc{#1}}}\n\\newcommand{\\ruleApp}[2][]{{\\normalfont\\textsc{#2}}\\scalebox{.6}{[#1]}}\n'),
	write(S, '\n\\begin{document}\n\n'),
	write(S, '\\begin{scaletikzpicturetowidth}{\\textwidth}\n'),
	( Style = 'tikzpicture' ->	
		write(S, '\\begin{tikzpicture}[scale=\\tikzscale, baseline=0pt, grow=down]\n'),
		write(S, '\\tikzset{level distance = 30pt}\n'),
		write(S, '\\tikzset{every tree node/.style={align=center,anchor=north}}\n'),
		write(S, '\\Tree\n'),
		drawTree_as_tikzpicture(Tree, S, 0, (1,_)), % ide of first variable
		write(S, '\\end{tikzpicture}\n')
	; Style = 'forest' ->	
		write(S, '\\scalebox{\\tikzscale}{\n\\begin{forest}\n'),
		write(S, 'for tree={align=center, parent anchor=south, child anchor=north, l sep=5mm}\n'),
		drawTree_as_forest(Tree, S, 0, (1,_)), % ide of first variable
		write(S, '\\end{forest}\n}\n')
	; report('Error: Unknown latex style tree'), fail
	), 
	write(S, '\\end{scaletikzpicturetowidth}\n'),
	write(S, '\\end{document}'),		
	close(S).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% drawTree_as_tikzpicture(Tree, S, Tabs)
% writes a latex code for the essential part of Tree
% in source S and traks the indentation by Tabs  

drawTree_as_tikzpicture(Tree, S, Tabs, (VC1, VC)) :-
	Tree = tree(Node, ChildList),
	nonvar(Node),
	Node = trnd(nd(Mods, LLF, Args, Sign), Id, Note, _),
	instantiate_vars_in_ttterm_list([LLF|Mods], VC1, VC2), % instantiate variables
	ttterm_to_tabLLF(LLF, PrLLF),
	maplist(ttterm_to_tabLLF, Mods, LatexMods),
	( LatexMods = [] ->  AtomMods = ''
	; atomic_list_concat(LatexMods, ', ', AtMods),
	  atomic_list_concat(['[', AtMods, '] : '], AtomMods) 
	),
	maplist(ttterm_to_tabLLF, Args, LatexArgs),
	atomic_list_concat(LatexArgs, ', ', AtomArgs),
	(Sign == true -> AtomSign = '\\T'; AtomSign = '\\F'),
	term_to_atom(Id, AtomId),
	rule_app_superscript(Note, RuleApp), 
	Tab2 is Tabs + 2,
	Tab1 is Tabs + 1,
	tab(S, Tabs), write(S, '[.\\node{ '),  %\\begin{tabular}{c}
	atomic_list_concat(['\\lab{', AtomId, '}~', RuleApp, '  '], Label),
	write(S, Label), write(S,'\n'), 
	atomic_list_concat(['$', AtomMods, PrLLF, ' : [', AtomArgs, '] : ', AtomSign, '$'], Formula),
	tab(S, Tab2), write(S, Formula), 
	( nonvar(ChildList), ChildList = closer([ClIDs, Rule]) -> 
		write(S, '\\\\[2mm]\n'),
		term_to_atom(ClIDs, AtClIDs),
		lambdaTerm_to_latex(Rule, RuleLatex),
		atomic_list_concat(['\\lab{\\phantom{0}}~$^{\\ruleApp', AtClIDs, '{', RuleLatex, '}}$  $\\btimes$'], ClNode),
		tab(S, Tab2),  write(S, ClNode)
	; true
	),	
	write(S, ' };\n'),  %\\end{tabular}
	( 	nonvar(ChildList), ChildList = [Node1|_], Node1 = tree(_,_) -> 
		drawTree_as_tikzpicture(Node1, S, Tab1, (VC2, VC3)); 
		VC3 = VC2 
	),
	( 	nonvar(ChildList), ChildList = [_,Node2], Node2 = tree(_,_) -> 
		drawTree_as_tikzpicture(Node2, S, Tab1, (VC3, VC)); 
		VC = VC3
	),
	tab(S, Tabs), write(S, ']\n').




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% drawTree_as_forest(Tree, S, Tabs)
% writes a latex code for the essential part of Tree
% in source S and traks the indentation by Tabs  

drawTree_as_forest(Tree, S, Tabs, (VC1, VC)) :-
	Tree = tree(Node, ChildList),
	nonvar(Node),
	Node = trnd(nd(Mods, LLF, Args, Sign), Id, Note, _),
	instantiate_vars_in_ttterm_list([LLF|Mods], VC1, VC2), % instantiate variables
	ttterm_to_tabLLF(LLF, PrLLF),
	maplist(ttterm_to_tabLLF, Mods, LatexMods),
	( LatexMods = [] ->  AtomMods = ''
	; atomic_list_concat(LatexMods, ', ', AtMods),
	  atomic_list_concat(['[', AtMods, '] : '], AtomMods) 
	),
	maplist(ttterm_to_tabLLF, Args, LatexArgs),
	atomic_list_concat(LatexArgs, ', ', AtomArgs),
	(Sign == true -> AtomSign = '\\T'; AtomSign = '\\F'),
	term_to_atom(Id, AtomId),
	rule_app_superscript(Note, RuleApp), 
	Tab2 is Tabs + 2,
	Tab1 is Tabs + 1,
	tab(S, Tabs), write(S, '[{'),  %\\begin{tabular}{c}
	atomic_list_concat(['\\lab{', AtomId, '}~', RuleApp, '  '], Label),
	write(S, Label), write(S,'\n'), 
	atomic_list_concat(['$', AtomMods, PrLLF, ' : [', AtomArgs, '] : ', AtomSign, '$'], Formula),
	tab(S, Tab2), write(S, Formula), 
	( nonvar(ChildList), ChildList = closer([ClIDs, Rule]) -> 
		write(S, '\\\\[2mm]\n'),
		term_to_atom(ClIDs, AtClIDs),
		lambdaTerm_to_latex(Rule, RuleLatex),
		atomic_list_concat(['\\lab{\\phantom{0}}~$^{\\ruleApp', AtClIDs, '{', RuleLatex, '}}$  $\\btimes$'], ClNode),
		tab(S, Tab2),  write(S, ClNode)
	; true
	),
	write(S, '}\n'),	
	( 	nonvar(ChildList), ChildList = [Node1|_], Node1 = tree(_,_) -> 
		drawTree_as_forest(Node1, S, Tab1, (VC2, VC3)); 
		VC3 = VC2 
	),
	( 	nonvar(ChildList), ChildList = [_,Node2], Node2 = tree(_,_) -> 
		drawTree_as_forest(Node2, S, Tab1, (VC3, VC)); 
		VC = VC3
	),
	tab(S, Tabs), write(S, ']\n').





%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Note to Rule application
rule_app_superscript([], '').

rule_app_superscript(Note, RApp) :-
	Note =.. [F, List | Rest],
	( Rest = [CnstList] -> 
      maplist(ttterm_to_tabLLF, CnstList, AtCnstList),
	  atomic_list_concat(AtCnstList, ', ', Cnst1),
	  atomic_list_concat(['~$', Cnst1, '$'] , Cnst)
	; Cnst = ''	
	),
	term_to_atom(List, AtomList),
	lambdaTerm_to_latex(F, LatexF),
	atomic_list_concat(['$^{\\ruleApp', AtomList, '{', LatexF, Cnst, '}}$'], RApp). 



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% TTterm into a tableau llf term
ttterm_to_tabLLF((Term, _Ty), Latex) :-
	var(Term),	
	!,
	term_to_atom(Term, Atom_term),
	atom_chars(Atom_term, [_, _ | Index_List]),
	atom_chars(Index, Index_List),
	atomic_list_concat(['X_{', Index, '}'], Latex).

ttterm_to_tabLLF((Term1 @ Term2, _Ty), Latex) :-
	!,
	ttterm_to_tabLLF(Term1, Latex1),
	ttterm_to_tabLLF(Term2, Latex2),
	( Term2 = (T, _),  nonvar(T),  T = _ @ _  ->
		atomic_list_concat([Latex1, ' ~ (', Latex2, ')'], Latex)
    ; atomic_list_concat([Latex1, ' ~ ', Latex2], Latex)
	).

ttterm_to_tabLLF((abst(X, TTerm), _Ty), Latex) :-
	!,
	ttterm_to_tabLLF(X, Latex_X),
	ttterm_to_tabLLF(TTerm, Latex1),
	atomic_list_concat(['(\\lambda ', Latex_X, '.\\,', Latex1, ')'], Latex).

ttterm_to_tabLLF( ((Term, Ty), _Type), Latex) :-
	!,
	ttterm_to_tabLLF((Term, Ty), Latex1),
	atomic_list_concat(['\\{', Latex1, '\\}'], Latex).

ttterm_to_tabLLF( (tlp(_,Term,_,_,_), Type), Latex ) :-
	!,
	( memberchk(Term, ['$','%','#']) -> 
		atomic_list_concat(['\\', Term], LatexTerm)
	; atomic_list_concat(Parts1, '&', Term),
	  atomic_list_concat(Parts1, '\\&', Temp1),
	  atomic_list_concat(Parts2, '_', Temp1),
	  atomic_list_concat(Parts2, '\\_', Temp2),
	  atomic_list_concat(Parts3, '$', Temp2),
	  atomic_list_concat(Parts3, '\\$', LatexTerm)
	),
	( is_synt_type(Type) ->
	  	atomic_list_concat(['\\synt{', LatexTerm, '}'], Latex)
	; atomic_list_concat(['{\\tt ', LatexTerm, '}'], Latex)
	).

ttterm_to_tabLLF( (C, _Ty), Latex ) :-
	atom_chars(C, [Symb | Index_List]),
	atom_chars(Index, Index_List),
	atomic_list_concat([Symb, '_{', Index, '}'], Latex).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% checks if type is a syntactic type
is_synt_type(A~>B) :-
	!, is_synt_type(A),
	is_synt_type(B).

is_synt_type(A) :-
	memberchk(A, [np:_, s:_, pp, n:_]).



test_atom_to_term :-
	tree_structure(Tree),
	term_to_atom(Tree, AtomTree),
	read_term_from_atom(AtomTree, Tree1, []),
	(Tree1 = Tree -> write('The same\n'); write('different\n')).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% instantiate vars in tt Term to print nice variables
instantiate_vars_in_ttterm( (T,_Ty), C1, C2 ) :-
	var(T), !,
	term_to_atom(C1, Ind),  
	atomic_list_concat(['x', Ind], T), 
	C2 is C1 + 1.

instantiate_vars_in_ttterm( (TT1 @ TT2,_Ty), C1, C2 ) :-
	!, instantiate_vars_in_ttterm(TT1, C1, C),
	instantiate_vars_in_ttterm(TT2, C, C2).

instantiate_vars_in_ttterm( (abst((X,_), TT), _Ty), C1, C2 ) :-
	!, 
	( var(X)  ->  
		term_to_atom(C1, Ind),  
		atomic_list_concat(['x', Ind], X), 
		C is C1 + 1
	; C = C1
	),
	instantiate_vars_in_ttterm(TT, C, C2).

instantiate_vars_in_ttterm( ((Term, Ty), _), C1, C2 ) :-
	!, instantiate_vars_in_ttterm((Term, Ty), C1, C2).

instantiate_vars_in_ttterm( _, C1, C1 ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
instantiate_vars_in_ttterm_list([], C1, C1).

instantiate_vars_in_ttterm_list([H|Rest], C1, C2) :-
	instantiate_vars_in_ttterm(H, C1, C),
	instantiate_vars_in_ttterm_list(Rest, C, C2).






	



