%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Description: Creates Latex File of Tableau Proof
%     Version: 12.06.12
%      Author: lasha.abzianidze{at}gmail.com 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% drawInLatex(Tree)
% Creates a latex file, writes preamble, 
% imports packages and writes beginings of Tree
	
drawInLatex :-
	tree_structure(Tree),
	(exists_directory('latex') -> true; make_directory('latex')),
	open('latex/tree.tex', write, S, [encoding(utf8)]),
	write(S, '\\documentclass{article}\n'),
	write(S, '\\usepackage{tikz-qtree-compat}\n'),
	write(S, '\\usepackage{amssymb}\n'),
	write(S, '\\usepackage{environ}\n'),
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
	write(S, '}\n'),
	write(S, '\\makeatother\n'),
	write(S, '\\newcommand{\\lab}[1]{\\mybox[fill=gray!30]{#1}}\n'),
	write(S, '\\newcommand\\mybox[2][]{\\tikz[overlay]\\node[fill=blue!20,inner sep=2pt, anchor=text, rectangle, rounded corners=1mm,#1] {#2};\\phantom{#2}}\n'),
	write(S, '\\newcommand{\\T}{\\mathbb{T}}\n\\newcommand{\\F}{\\mathbb{F}}\n'),
	write(S, '\\begin{document}\n'),
	tab(S, 2), write(S, '\\begin{scaletikzpicturetowidth}{\\textwidth}\n'),	
	tab(S, 2), write(S, '\\begin{tikzpicture}[scale=\\tikzscale, baseline=0pt, grow=down]\n'),
	tab(S, 4), write(S, '\\tikzset{level distance = 30pt}\n'),
	tab(S, 4), write(S, '\\Tree\n'),
	drawTreeInLatex(Tree, S, 6),
	tab(S, 2), write(S, '\\end{tikzpicture}\n'),
	tab(S, 2), write(S, '\\end{scaletikzpicturetowidth}\n'),
	write(S, '\\end{document}'),		
	close(S).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% drawTreeInLatex(Tree, S, Tabs)
% writes a latex code for the essential part of Tree
% in source S and traks the indentation by Tabs  

drawTreeInLatex(Tree, S, Tabs) :-
	Tree = tree(Node, ChildList),
	nonvar(Node),
	Node = trnd(nd(Mods, LLF, Args, Sign), Id, Note, _),
	%term_to_atom(LLF, AtomLLF),
	ttTerm_to_latexTerm(LLF, PrLLF),
	maplist(ttTerm_to_latexTerm, Mods, LatexMods),
	atomic_list_concat(LatexMods, ', ', AtomMods),
	maplist(ttTerm_to_latexTerm, Args, LatexArgs),
	atomic_list_concat(LatexArgs, ', ', AtomArgs),
	%atomic_list_concat(ListAtomArgs, '\'', UglyAtomArgs),
	%atomic_list_concat(ListAtomArgs, '', AtomArgs),
	(Sign == true -> AtomSign = '$\\T$'; AtomSign = '$\\F$'),
	term_to_atom(Id, AtomId),
	term_to_atom(Note, AtomNote1),
	lambdaTerm_to_latex(AtomNote1, AtomNote),
	Tabs4 is Tabs + 4,
	Tabs2 is Tabs + 2,
	tab(S, Tabs), write(S, '[. \\node{'), nl(S),  %\\begin{tabular}{c}
	atomic_list_concat(['\\lab{', AtomId, '}', '$^{~', AtomNote, '}$', '\\\\'], Label),
	tab(S, Tabs4), write(S, Label), nl(S),
	%atomic_list_concat(ListLLF, 'abst(', AtomLLF),
	%atomic_list_concat(ListLLF, '$\\lambda($', PrLLF),
	atomic_list_concat(['\\tt{', '{[', AtomMods, ']}:~', PrLLF, ':~{[', AtomArgs, ']}:~', AtomSign, '} \\\\'], Formula),
	tab(S, Tabs4), write(S, Formula), nl(S),
	
	%tab(S, Tabs4), write(S, PrLLF), write(S, ' \\\\'), nl(S),
	%tab(S, Tabs4), write(S, '{'), write(S, AtomArgs), write(S, '} \\\\'), nl(S),
	%tab(S, Tabs4), write(S, '\\tt{'), write(S, AtomNote), write(S, '} \\\\'), nl(S),
	
	tab(S, Tabs2), write(S, '};'), nl(S),  %\\end{tabular}
	( 	nonvar(ChildList), ChildList = [Node1|_], Node1 = tree(_,_) -> 
		drawTreeInLatex(Node1, S, Tabs2); 
		true 
	),
	( 	nonvar(ChildList), ChildList = [_,Node2], Node2 = tree(_,_) -> 
		drawTreeInLatex(Node2, S, Tabs2); 
		true 
	),	
	tab(S, Tabs), write(S, ']'), nl(S).

	
