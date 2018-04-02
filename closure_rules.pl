:- multifile r/4.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% 		       Closure Rules
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% closure related to concept subsumption
r(cl_subsumption, 	closure, _, 
		br([nd( M1, TT1, Args1, true ),
			nd( M2, TT2, Args2, false )
		   ],
		  Sig)
		===>
		br([nd( [], (true, t), [], false )],
		  Sig) ) 
:-
			match_list_ttTerms(Args1, Args2), %!!! why not Args1=Args2?
			once( ( M2 = []
				  ; match_list_only_terms(M1, M2) ) ),
			(%TT1 = TT2; %because features in types
	 			match_ttTerms(TT1, TT2) % ignoring tokens and heads 
	 		; 	ttTerm_to_informative_tt(TT1, (Term1, _Type1)),
				ttTerm_to_informative_tt(TT2, (Term2, _Type2)),
				% not necessary, context defines them of the same time
				%luc(Type1, Type2, _GenType), % mortal:np~>s @ x = mortal:n @ x
	 			%TT1 = (tlp(_,Term1,_,_,_), Type),
	 			%TT2 = (tlp(_,Term2,_,_,_), Type),	
	 			atom(Term1),
				atom(Term2),	 
				isa(Term1, Term2)
				%Term1 =@= Term2 % no background knowledge
	 		%alpha(Norm1, Norm2)
			). 


% closure related to comlex concept subsumption (dirty addition to cl_subsumption)
r(cl_subsumption_complex, 	closure, _, 
		br([nd( M1, (TTmod1@TT1, Ty1), Args1, true ),
			nd( M2, (TTmod2@TT2, Ty2), Args2, false )
		   ],
		  Sig)
		===>
		br([nd( [], (true, t), [], false )],
		  Sig) ) 
:-
			luc(Ty1, Ty2, _Type),
			match_list_ttTerms(Args1, Args2),
			once( ( M2 = []
				  ; match_list_only_terms(M1, M2) ) 
				),
			match_ttTerms(TTmod1, TTmod2), % ignoring tokens and heads 
	 		ttTerm_to_informative_tt(TT1, (Term1, _Type1)),
			ttTerm_to_informative_tt(TT2, (Term2, _Type2)),
	 		atom(Term1),
			atom(Term2),	 
			isa(Term1, Term2).


% closure related to "There is"
r(contra_there, 	closure, _, 
		br([nd( [], (((tlp(_,'be',_,_,_),_) @ TT, _) @ (tlp(_,'there',_,_,_),np:thr), s:_) ,
				[], false )],
		  Sig)
		===>
		br([nd( [], (true, t), [], false )], % only semnatic terms
		  Sig) ) 
:-
			debMode('no_gq_llfs') ->
				TT = (Term, _),
				( atom(Term); Term=.. [tlp | _])
			;	true.


% closure related to verb subcategorization
r(cl_subcat, 	closure, _,  %sick-1881
		br([nd( _, (Tr1, Ty1), Args1, true ),
			nd( [], (Tr2, Ty2), Args2, false )
		   ],
		  Sig)
		===>
		br([nd( [], (true, t), [], false )],
		  Sig) ) 
:-
			( Tr1 =@= Tr2 % avoids matching variable to term, var(X) for variables can slove the global problem
			; Tr1 = tlp(_,Lm,_,_,_), Tr2 = tlp(_,Lm,_,_,_) 
			),
			Ty1 = np:_~>TyS1,
			final_value_of_type(TyS1, s:_),
			Ty2 = np:_~>TyS2,
			final_value_of_type(TyS2, s:_),
			append(_, Args2, Args1), !.


% closure about Verb particle-arg vs PrepPhrase
% jump over : c1,c2 = not (over c1: jump: c2)
r(cl_vp_pr_arg_pp, 	closure, _,  %sick-150
		br([nd( M1, ((tlp(_,Jump,_,_,_), _)@(tlp(_,Over,_,_,_), pr), _), Args1, TF1 ),
			nd( M2, (tlp(_,Jump,_,_,_), _), Args2, TF2 )
		   ],
		  Sig)
		===>
		br([nd( [], (true, t), [], false )],
		  Sig) ) 
:-
			( member( ((tlp(_,Over,_,_,_),_) @ C, _VP_mod),  M2),
				(TF1, TF2) = (false, true),
				M1 = []
			; M2 = [((tlp(_,Over,_,_,_),_) @ C, _)],
				(TF1, TF2) = (true, false)
			), 
			append(P1, P2, Args2),
			append([P1, [C], P2], Args1), !.


% closure related to antonym words
/*r(cl_ant_cnst, 		closure, _,
		br([nd( _, (tlp(_,Lm1,_,_,_), Ty1), Args, true ),
			nd( _, (tlp(_,Lm2,_,_,_), Ty2), Args, true )
		   ],
		  Sig)
		===>
		br([nd( [], (true, t), [], false )],
		  Sig) ) 
:-
			cat_eq(Ty1, Ty2),
			ant_wn(Lm1, Lm2), !.*/

r(cl_ant_n_mod, 		closure, _, %fracas-204,205
		br([nd( _, ((tlp(_,Lm1,_,_,F1), n:_~>n:_) @ N, n:_), Args, true ),
			nd( _, ((tlp(_,Lm2,_,_,F2), n:_~>n:_) @ N, n:_), Args, true )
		   ],
		  Sig)
		===>
		br([nd( [], (true, t), [], false )],
		  Sig) ) 
:-
			F1 \= 'COL', F2 \= 'COL',
			ant_wn(Lm1, Lm2), !.


% C1 did C2, Dance(C2) -> Danced(C1)
r(contra_do_vp, 	closure, _, 
		br([nd( M1, (tlp(_,'do',_,_,_), np:_~>np:_~>s:_), 	[C2, C1], 	TF1 ),
		    nd( _, (tlp(_,Dance,'NN',_,_), n:_),			[C2],		TF2 ),
		    nd( M3, (tlp(_,Dance,_,_,_), np:_~>s:_),		[C1],		TF3 )
		   ],
		  Sig)
		===>
		br([nd( [], (true, t), [], false )], % only semnatic terms
		  Sig) ) 
:-
			(	(TF1, TF2, TF3) = (true, true, false), M3 = [] 
			;	(TF1, TF2, TF3) = (false, true, true), M1 =[]
			).


% bottle of beer = beer bottle
% sick-3275, sick-7477
r(cl_noun_adj_comp, 	closure, _, 
		br([nd( M1, ((tlp(_,Bottle,_,_,_), pp~>n:_) @ (OF @ C2, pp), n:_), 				[C1], 	TF1 ),
		    nd( _,  (tlp(_,Beer,_,_,_), n:_),											[C2],	TF2 ),
			nd( M3, ((tlp(_,Beer,_,_,_), n:_~>n:_) @ (tlp(_,Bottle,_,_,_), n:_), n:_), 	[C1],	TF3 )
		   ],
		  Sig)
		===>
		br([nd( [], (true, t), [], false )],
		  Sig) ) 
:-
			OF = (tlp(_,_Of,'IN',_,_), np:_~>pp),
			(	(TF1, TF2, TF3) = (true,  true, false), M3 = [] 
			;	(TF1, TF2, TF3) = (false, true, true),  M1 = []
			).


% closure related to an instance of a predicate
r(cl_instance, 	closure, _,  
		br([nd( [], (tlp(_,Term,_,_,_),_), Args, TF )],
		  Sig)
		===>
		br([nd( [], (true, t), [], false )],
		  Sig) ) 
:-
			tt_atomList_to_atomList(Args, AtomArgs),
			( TF = false -> instance(AtomArgs, Term)
			; TF = true, not_instance(AtomArgs, Term)
			). 


% closure related to concept disjunction
r(cl_disjoint, 	closure, _, 
		br([nd( _, TT1, Args, true ),
			nd( _, TT2, Args, true )
		   ],
		  Sig)
		===>
		br([nd( [], (true, t), [], false )],
		  Sig) ) 
:-
			%match_list_ttTerms(Args1, Args2), %!!! why not Args1=Args2?
			ttTerm_to_informative_tt(TT1, (Term1, Type1)),
			ttTerm_to_informative_tt(TT2, (Term2, Type2)),
			cat_eq(Type1, Type2),
			%TT1 = (tlp(_,Term1,_,_,_), Type),
			%TT2 = (tlp(_,Term2,_,_,_), Type),	
			atom(Term1),
			atom(Term2),	 
			once( 	disjoint(Term1, Term2)%; % gives weird results with subWN: disjoint(frog,hold), disjoint(reserve,reserve)
					%disjoint_sym(Term1, Term2)	
					%(\+isa(Term1, Term2), \+isa(Term2, Term1)) % super strict
					%\+(isa(Term1, Top), isa(Term2, Top) )
			). 


% closure by adjective+noun construction, when compund noun is false
% small animal: c: F, small: c: T, animal: c: T
% sick-2791
r(cl_adj_noun_1, 	closure, _, 
		br([nd( [], ((TLP_adj1, n:_~>n:_) @ TTn, n:_), Args, false ),
			nd( _, TTn, Args, true ),
			nd( _, (TLP_adj2, np:_~>s:_), Args, true ) %non-empty modlist
		   ],
		  Sig)
		===>
		br([nd( [], (true, t), [], false )],
		  Sig) ) 
:-
			
			TLP_adj1 = tlp(_,Adj,_,_,_),
			TLP_adj2 = tlp(_,Adj,_,_,_). 


% closure by adjective+noun construction, when compound noun is true
% small animal: c: T, small: c: F, animal: c: T %!!! maybe change truth values here? F,T,T?
% sick-7466, 
/*
r(cl_adj_noun_2, 	closure, _, 
		br([nd( _, ((TLP_adj1, n:_~>n:_) @ TTn, n:_), Args, true ), %non-empty modlist
			nd( _, TTn, Args, true ),
			nd( [], (TLP_adj2, np:_~>s:_), Args, false )
		   ],
		  Sig)
		===>
		br([nd( [], (true, t), [], false )],
		  Sig) ) 
:-
			
			TLP_adj1 = tlp(_,Adj,_,_,_),
			TLP_adj2 = tlp(_,Adj,_,_,_). 
*/

% closure rule about exactly_N
% fracas-85
r(cl_exact_num, 	closure, _, 
		br([nd( _, ((((TLP_RB, (n:_~>(np:_~>s:_)~>s:_)~>n:_~>(np:_~>s:_)~>s:_) @ TT_CD1, _) @ TTn, _) @ TTvp, s:_),  Args, true ),
			nd( _, (((tlp(_,Lm2,POS,_,_), n:_~>(np:_~>s:_)~>s:_) @ TTn, _) @ TTvp, s:_), Args, true )
		   ],
		  Sig)
		===>
		br([nd( [], (true, t), [], false )],
		  Sig) ) 
:-
			member(POS, ['DT', 'CD']), % a_few=DT, one=CD
			TLP_RB = tlp(_,Lm_RB,_,_,_),
			TT_CD1 = (tlp(_,Lm1,'CD',_,_), n:_~>(np:_~>s:_)~>s:_), %!!! DT also?
			member(Lm_RB, ['exactly', 'just']),
			is_greater(Lm2, Lm1), 
			!.


% closure for  {"c wears a/s white cloth"=F, "d is white"=T, "c is in d"=T}
% not true     {"c wears a/s white cloth"=T, "d is white"=T, "c is in d"=F} 
%!!!but we allow both cases and it is interesting what type of unsoundness it will evoke
% sick-218, sick-9136
r(cl_wear_cloth, 	closure, _, 
		br([ nd( M1, (tlp(_,'in','IN',_,_),_), [C1, C2], TF_in ),
			 nd( M2, ((Det_TT @ TT_Cloth1, (np:_~>s:_)~>s:_) @ (abst(X, (( (tlp(_,'wear',_,_,_),_) @ X, _) @ C2, _)), _), s:_),  [], TF_wear),
			 nd( _, (tlp(_,Cloth2,_,_,_), n:_), [C1],  true )
		   ],
		  Sig)
		===>
		br([nd( [], (true, t), [], false )],
		  Sig) ) 
:-
			Det_TT = (tlp(_,Det,'DT',_,_), n:_~>(np:_~>s:_)~>s:_),
			once(member(Det, ['a', 's', 'the'])), %!!! simplified
			( (TF_in, M1, TF_wear, M2) = (true, _, false, [])
			; (TF_in, M1, TF_wear, M2) = (false, [], true, _)
			), 
      		!,
			( TT_Cloth1 = ((tlp(_,Cloth2,_,_,_COL),_) @ (tlp(_,Cloth,_,_,_),n:_), n:_), %sick-218
			  ( once(member(Cloth, ['cloth', 'clothes']))
			  ; word_hyp(Cloth, 'clothing', _) %relaxing constraints
			  )
			; 
			  TT_Cloth1 = (tlp(_,Cloth2,_,_,_), _), %sick-9136
			  word_hyp(Cloth2, 'clothing', _)
			), !.
			  
			  

			







