%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Description: GUI for Tableau Tree
%     Version: 12.06.12
%      Author: lasha.abzianidze{at}gmail.com 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- module(gui_tree, 
	[
		displayTree/3
	]).

:- use_module(library(pce)).
:- use_module('../latex/latex', [drawInLatex/1, tree_structure/1]).
:- use_module('../utils/user_preds', [
	remove_adjacent_duplicates/2, all_pairs_from_set/2, writeln_list/1,
	list_to_set_using_match/2, term_list_concat/2
	]).	
:- use_module('../printer/reporting', [report/1]).	
:- use_module('../llf/ttterm_to_term', [ttTerm_to_prettyTerm/2, ttTermList_to_prettyTermList/2]).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- dynamic font_size/1.
font_size(nil).

displayTree(Tree, FontSize, Problem_Id) :-
	retract(tree_structure(_)),
	asserta(tree_structure(Tree)),
	%retract(current_problem_id(_)),
	%asserta(current_problem_id(Problem_Id)),
	%Tree = tree(trnd(nd(_, _, _, _), _, _, NodeRef), _), report('NodeRef right after asserting a Tree: ', NodeRef),
	retract(font_size(_)),
	asserta(font_size(FontSize)),
	term_list_concat(['Natural Tableau: problem ID = ', Problem_Id], FrameTitle),
	new(Frame, frame(FrameTitle)),
	send(Frame, open),
	send(Frame, append, new(Pic, picture)),
	send(Pic, height, 600),
	problem_to_multilineText(Problem_Id, Text),
	send(Pic, display, new(TxtRef, text(Text, center, font(screen, roman, FontSize)))),
	send(new(Menu, dialog), above, Pic),
	send(Menu, append, new(MB, menu_bar)),
	send(MB, append, new(File, popup('File'))),
	send(File, append, menu_item(export_as_tikzpicture, message(@prolog, drawInLatex, tikzpicture), 'Export as LaTex (Tikzpicture)')),
	send(File, append, menu_item(export_as_forest, message(@prolog, drawInLatex, forest), 'Export as LaTex (Forest)')),
	send(MB, append, new(View, popup('View'))),
	send(View, append, menu_item(zoom_in, message(@prolog, zoom, Pic, TxtRef, in), 'Zoom in')), %zoom(Pic, TxtRef, Mode) 
	send(View, append, menu_item(zoom_out, message(@prolog, zoom, Pic, TxtRef, out), 'Zoom out')),
	send(View, append, menu_item(zoom_in_x2, message(@prolog, zoom, Pic, TxtRef, in_x2), '2 x Zoom in')),
	send(View, append, menu_item(zoom_out_x2, message(@prolog, zoom, Pic, TxtRef, out_x2), '2 x Zoom out')),
	startTree(Pic, TxtRef, Tree, FontSize).
	
	
startTree(Pic, TxtRef, Tree, FontSize) :-	
	new(Link, link(in, out, line(arrows := second))),
	%problem_to_multilineText(Problem_Id, Text),
	%send(Pic, display, new(ProbText, text(Text, center, font(screen, roman, FontSize)))),

	send(TxtRef, font, font(screen, roman, FontSize)),

	%Tree = tree( trnd(nd(_,Prem,_,_), _,_,_), [ConcTree|_]),
	%nonvar(ConcTree),
	%ConcTree = tree( trnd(nd(_,Conc,_,_),_,_,_), _),
	%ttTerm_to_pretty_ttTerm(Prem, PPprem),
	%ttTerm_to_pretty_ttTerm(Conc, PPconc),
	%term_to_atom(PPprem, Pr),
	%term_to_atom(PPconc, Co),
	%atomic_list_concat([Pr, ' ===>\n', Co], Label),
	%send(Pic, display, new(Title, text(Label, center, font(screen, roman, 14)))),
	%get(Title, width, W),
	get(TxtRef, width, W),
	get(TxtRef, height, H),
	send(TxtRef, y(0)),
	Y is H + 10,
	displayTreeXY(Pic, Tree, FontSize, _, C, Y, _, Width, _, Link, Tree),
	X is C - W//2, 
	send(TxtRef, x(X)),
	send(Pic, width, Width + 80).
	%send(Pic, height, 600).
	

problem_to_multilineText(Problem_Id, Text) :-
	sen_id(_, Problem_Id, _, Answer, _), !,
	findall(IdSen, 
			(sen_id(Id, Problem_Id, 'p', Answer, Sent), atomic_list_concat([Id, ': ', Sent], IdSen)), 
			ListPrem
	),
	atomic_list_concat(ListPrem, '\n', PremText),
	findall(IdSen, 
			(sen_id(Id, Problem_Id, 'h', Answer, Sent), atomic_list_concat([Id, ': ', Sent], IdSen)), 
			ListHypo
	),
	atomic_list_concat(ListHypo, '\n', HypoText),
	atomic_list_concat(['--------------------------- ', Answer, ' ---------------------------'], Delim),
	atomic_list_concat([PremText, Delim, HypoText], '\n', Text).
	
% Draw tree with one child	
displayTreeXY(Pic, SubTree, FontSize, X, C, Y, UpWidth, NewDwWidth, RootRef, Link, Tree) :-
	%nonvar(SubTree),
	SubTree = tree(Root, [Child]),
	%\+ is_list(Left),
	nonvar(Child),
	Child =.. [tree | _],
	!,
	%(nonvar(RootRef) -> report('before Draw a root w a child, RootRef is bound: ', RootRef); true),
	drawMotherNode(Pic, Root, FontSize, RootRef),
	get(RootRef, width, RootW),
	send(RootRef, y, Y),
	(nonvar(UpWidth) -> max_list([RootW, UpWidth],NewUpWidth); NewUpWidth = RootW),
	NewY is Y + ceil(100 * FontSize / 11),
	displayTreeXY(Pic, Child, FontSize, X, C, NewY, NewUpWidth, DwWidth, ChildRef, Link, Tree),
	max_list([RootW, DwWidth], NewDwWidth),
	RootX is C - RootW//2, 	
	send(RootRef, x, RootX),
	send(RootRef, connect, ChildRef, Link).
	
	
% Draw tree with two children	
displayTreeXY(Pic, SubTree, FontSize, X, C, Y, UpWidth, NewDwWidth, RootRef, Link, Tree) :-
	%nonvar(SubTree),
	SubTree = tree(Root, [Left, Right]),
	nonvar(Left),
	nonvar(Right), !,
	drawMotherNode(Pic, Root, FontSize, RootRef),
	get(RootRef, width, RootW),
	send(RootRef, y, Y),
	NewY is Y + ceil(100 * FontSize / 12),
	max_list([RootW, UpWidth], NewUpWidth),
	Gap = 30,
	displayTreeXY(Pic, Left, FontSize, X, _, NewY, NewUpWidth//2, LDwWidth, LeftChildRef, Link, Tree),
	RX is X + LDwWidth + Gap,
	displayTreeXY(Pic, Right, FontSize, RX, _, NewY, NewUpWidth//2, RDwWidth, RightChildRef, Link, Tree),
	NewDwWidth = LDwWidth + RDwWidth + Gap,
	C is X + NewDwWidth//2,
	RootX is C - RootW//2, 	
	send(RootRef, x, RootX),
	send(RootRef, connect, LeftChildRef, Link),
	send(RootRef, connect, RightChildRef, Link).

	
% Draw leaf		
displayTreeXY(Pic, SubTree, FontSize, X, C, Y, UpWidth, NewDwWidth, RootRef, _, Tree) :-
	%nonvar(SubTree),
	SubTree = tree(Root, ClosureIDList),
	%(var(Left); is_list(Left)),
	\+is_list(ClosureIDList), 
	nonvar(X), !,
	drawMotherNode(Pic, Root, FontSize, RootRef),
	get(RootRef, width, W),
	max_list([W, UpWidth], NewUpWidth),
	C is X + NewUpWidth//2,
	NewX is C - W//2,  	
	send(RootRef, x, NewX),
	send(RootRef, y, Y),
	NewDwWidth = NewUpWidth,
	( ClosureIDList = closer([IDs, RuleId]), nonvar(RuleId) -> 
		boldClosureNodes(IDs, Tree),
		displayClosureIDs(Pic, [IDs, RuleId], C, Y, FontSize, _NodeRef) 
	  ; 
	  ClosureIDList == 'Model' ->
		send(RootRef, colour, colour(@default, 60000, 0, 0));
		true ). 	

	
% Draw the most left leaf		
displayTreeXY(Pic, SubTree, FontSize, X, C, Y, UpWidth, NewDwWidth, RootRef, _, Tree) :-
	%nonvar(SubTree),
	SubTree = tree(Root, ClosureIDList),
	%(var(Left); is_list(Left)),
	\+is_list(ClosureIDList),
	var(X), !,
	drawMotherNode(Pic, Root, FontSize, RootRef),
	get(RootRef, width, W),
	max_list([UpWidth, W], NewUpWidth),
	C is NewUpWidth//2 + 10, 
	X is C - W//2, 	
	send(RootRef, x, X),
	send(RootRef, y, Y),
	NewDwWidth = NewUpWidth,
	( ClosureIDList = closer([IDs, RuleId]), nonvar(RuleId) -> 
		boldClosureNodes(IDs, Tree), 	
		displayClosureIDs(Pic, [IDs, RuleId], C, Y, FontSize, _NodeRef) 
	  ;
	  ClosureIDList == 'Model' ->
		send(RootRef, colour, colour(@default, 60000,0,0));
		true ). 



drawMotherNode(Pic, Node, FontSize, NodeRef) :-
	%(nonvar(NodeRef) -> report('!!! reference is bound in the begining of drawMothernode: ', NodeRef); true),
	%(var(NodeRef) -> report('Node is', Node); true),
	Node = trnd(nd(TTmods, TTterm, TTargs, Sign), Id, RuleApp, NodeRef),
	ttTerm_to_prettyTerm(TTterm, LLF),
	term_to_atom(LLF, AtomLLF),
	% TTmods
	ttTermList_to_prettyTermList(TTmods, Mods),
	term_to_atom(Mods, UglyAtomMods),
	atomic_list_concat(ListAtomMods, '\'', UglyAtomMods),
	atomic_list_concat(ListAtomMods, '', AtomMods),
	% TTargs
	ttTermList_to_prettyTermList(TTargs, Args),
	term_to_atom(Args, UglyAtomArgs),
	atomic_list_concat(ListAtomArgs, '\'', UglyAtomArgs),
	atomic_list_concat(ListAtomArgs, '', AtomArgs),
	(Sign == true -> AtomSign = 'TRUE'; AtomSign = 'FALSE'),
	term_to_atom(Id, AtomId),
	term_to_atom(RuleApp, AtomRuleApp1),
	atomic_list_concat(AtomRuleApp2, '\'', AtomRuleApp1),
	atomic_list_concat(AtomRuleApp2, '', AtomRuleApp),
	concat_atom([AtomId, ':', AtomRuleApp, '\n', AtomMods, '\n', AtomLLF, '\n', AtomArgs, '\n', AtomSign], Label),
	%(for_test('true') -> write('before printing mother node:'), writeln(Label); true),
	(nonvar(NodeRef) -> 
		%report('!!! NodeRef is bound while drawing a node: ',NodeRef),
		send(NodeRef, font, font(screen, roman, FontSize))
	  ; send(Pic, display, new(NodeRef, text(Label, center, font(screen, roman, FontSize))))
	),
	%send(Pic, display, new(NodeRef, text(Label, center, font(screen, roman, FontSize)))), %Font Size of Nodes
	%(for_test('true') -> write('after printing mother node:'), writeln(Label); true),
	send(NodeRef, recogniser, new(move_gesture(left))),
	send(NodeRef, handle, handle(w/2, h, in)),
	send(NodeRef, handle, handle(w/2, 0, out)).	




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% draws closure info as a node
displayClosureIDs(Pic, ClRuleApp, C, Y, FontSize, NodeRef) :-
	drawClosureIDs(Pic, ClRuleApp, FontSize, NodeRef),
	get(NodeRef, width, W),
	%max_list([W, UpWidth], NewUpWidth),
	%C is X + NewUpWidth//2,
	NewX is C - W//2,  	
	send(NodeRef, x, NewX),
	NewY is Y + ceil(100 * FontSize / 12),
	send(NodeRef, y, NewY). 

drawClosureIDs(Pic, [ClIDs, RuleId], FontSize, NodeRef) :-
	ClRuleApp =.. [RuleId, ClIDs],
	term_to_atom(ClRuleApp, Atom),
	(nonvar(NodeRef) -> 
		%report('!!! NodeRef is bound while drawing a node: ',NodeRef),
		send(NodeRef, font, font(screen, roman, FontSize))
	  ; send(Pic, display, new(NodeRef, text(Atom, center, font(screen, roman, FontSize))))
	),	
	send(NodeRef, colour, colour(@default, 60000,0,0)),
	get(NodeRef, font, font(Family, _, Points)),
	send(NodeRef, font, font(Family, bold, Points)),
	send(NodeRef, recogniser, new(move_gesture(left))),
	send(NodeRef, handle, handle(w/2, h, in)),
	send(NodeRef, handle, handle(w/2, 0, out)).	


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% boldClosureNodes(ClosureIDs, Tree)
% Finds closure nodes by their ids in Tree and makes them bold
boldClosureNodes([Id | RestIds], Tree) :-
	findSubTree(Tree, Id, SubTree),
	SubTree = tree(trnd(_,Id,_,Ref),_ChildList),
	nonvar(Ref), % should avoid error
	get(Ref, font, font(Family, _, Points)),
	send(Ref, font, font(Family, bold, Points)),
	!,
	boldClosureNodes(RestIds, Tree).

boldClosureNodes([], _).	


	
zoom(Pic, TxtRef, Mode) :-
	font_size(OldFontSize),
	(Mode = in, Size is OldFontSize + 1;
	 Mode = out, Size is OldFontSize - 1;
	 Mode = in_x2, Size is OldFontSize * 2;
	 Mode = out_x2, Size is ceil(OldFontSize / 2)),
	!,
	(Size < 1 -> FontSize = 1; FontSize = Size),  	
	tree_structure(TTree),
	TTree = tree(trnd(nd(_, _, _, _), _, _, NodeRef), _),
	%report('NodeRef right after retriveing the tree:\n', NodeRef),
	( var(NodeRef) ->
		send(Pic, clear)
	  ; true
	),
	startTree(Pic, TxtRef, TTree, FontSize),
	retract(font_size(_)),
	asserta(font_size(FontSize)).
	






