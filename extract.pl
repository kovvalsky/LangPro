% Print all lexical rules
print_all_lx_rules :-
	findall(Tree, ccg(_, Tree), CCGTrees),
	maplist(print_lx_rules, CCGTrees).

print_lx_rules(Tree) :- 
	Tree =.. [t | _] ->
		true;
	Tree =.. [lx | _] ->
		term_to_atom(Tree, A_Tree),	
		writeln(A_Tree);
	(Tree =  fa(_, A, B); 
	 Tree =  ba(_, B, A);
	 Tree =  fc(_, A, B);
	 Tree =  bc(_, B, A);
	 Tree = fxc(_, A, B);
	 Tree = bxc(_, B, A);
	 Tree = conj(_, _, A, B);
	 Tree = gbxc(_, 2, A, B);
	 Tree = gfxc(_, 2, B, A))  -> 
		print_lx_rules(A), 
		print_lx_rules(B);
	(Tree = tr(_, A);
	 Tree = lp(_, _, A);
	 Tree = rp(_, A, _);
	 Tree = ltc(_, _, A);
	 Tree = rtc(_, A, _)) ->
		print_lx_rules(A);  
	writeln('ERROR in getting CCGterms').



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
print_used_lexical_rules( _, (X, _) ) :-
	var(X), !.

print_used_lexical_rules( Id, (A @ B, _) ) :-
	!, print_used_lexical_rules(Id, A),
	print_used_lexical_rules(Id, B).

print_used_lexical_rules( Id, ((A, Ty), Type) ) :-
	!, type_to_pretty_type(Ty, P_Ty),
	type_to_pretty_type(Type, P_Type),
	term_to_atom(P_Ty, A_Ty),
	term_to_atom(P_Type, A_Type),
	ttTerm_to_prettyTerm((A, Ty), AtomTerm), 
	write(Id), write(': '), write(AtomTerm), write(': '),
	write(A_Ty), write(' ----> '), writeln(A_Type),
	print_used_lexical_rules(Id, (A, Ty)). 

print_used_lexical_rules( Id, (abst(_,A), _) ) :-
	!, print_used_lexical_rules(Id, A).

print_used_lexical_rules( _, (TLP, _) ) :-
	TLP =.. [tlp|_].




type_to_pretty_type(A:X, B) :-
	var(X) -> 
	B = A;
	B = A:X.	
type_to_pretty_type(A~>B, A1~>B1) :-
	type_to_pretty_type(A, A1),
	type_to_pretty_type(B, B1).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% extract used tableau rules from history & print












