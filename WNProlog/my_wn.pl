:- ensure_loaded([wn_s,
				  %wn_h_,		
				  wn_hyp
				 ]).
				 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
% extending hyp relation and cerates new file
:- dynamic h_/3.

h_(A, B, 0) :-
	hyp(A, B).	

extend_ord_hyp(L0) :-
	L1 is L0 + 1,
	findall(h_(A,C,L1), (h_(A,B,L0), hyp(B,C)), Assert),
	length(Assert, N),
	writeln(N),
	( N = 0 ->
		true;
		maplist(assertz, Assert),
		extend_ord_hyp(L1) ).

write_extended_hyp :-
	open('wn_h_.pl', write, S, [encoding(utf8)]),
	extend_ord_hyp(0),
	ignore((h_(A,B,O), 
			term_to_atom(h_(A,B,O), At), 
			atomic_list_concat([At, '.\n'], Wr), 
			write(S, Wr),
			fail )),
	close(S).

	




	
		
		
