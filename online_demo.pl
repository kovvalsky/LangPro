%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Contains predicates used for online version
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


online_demo(ID) :- 
	\+sen_id(_,ID,_,_,_),
	!,
	report(['There is no problem with ID=', ID, ' in the selected data set']).
	

online_demo(ID) :- 
	%report(['Entering online_demo/1\n']),
	%entail(1, _Answer, Provers_Answer, Closed, FinalStatus),
	print_problem(ID),
	problem_to_ttTerms('align', ID, Prems, Hypos, Align_Prems, Align_Hypos),
	check_problem(Align_Prems, Align_Hypos, 'yes', _, Al_Cl_yes, Al_St_yes, Al_Tr_yes),
	( Al_St_yes \== 'Defected' -> 
		check_problem(Align_Prems, Align_Hypos, 'no', _,  Al_Cl_no, Al_St_no, Al_Tr_no),
		check_problem(Prems, Hypos, 'yes', _, Cl_yes, St_yes, Tr_yes),
		check_problem(Prems, Hypos, 'no', _,  Cl_no, St_no, Tr_no),
		( Al_Cl_yes == 'closed' -> 
			YES = ['al', Al_Cl_yes, Al_St_yes],
			Tree_yes = Al_Tr_yes 
		; YES = ['na', Cl_yes, St_yes],
			Tree_yes = Tr_yes  
		),
		( Al_Cl_no ==  'closed' -> 
			NO  = ['al', Al_Cl_no,  Al_St_no],
			Tree_no = Al_Tr_no 
		; NO  = ['na', Cl_no,  St_no],
			Tree_no = Tr_no  
		), 
		atomic_list_concat(['yes' | YES], '_', Yes_File),
		atomic_list_concat([ 'no' | NO],  '_', No_File),
		output_XML(Tree_yes, ID, Yes_File),
		output_XML(Tree_no,  ID, No_File),
		format('~w, ~w~n', [Yes_File, No_File])	
	; YES = 'yes_NA', NO = 'no_NA',
		format('~w, ~w~n', [YES, NO])	
	).

print_problem(ID) :-
	findall(Prem, sen_id(_, ID, 'p', _, Prem), Prems),
	( sen_id(_, ID, 'h', Ans, Hypo) ->
		report(['ID = ', ID, ',   Gold Answer = ', Ans]),
		atomic_list_concat(Prems, '\n', Prems1),
		format('  ~w~n? ~w~n', [Prems1, Hypo])	
	; report(['There is no problem with ID=', ID, ' in the selected data set'])	
	).




