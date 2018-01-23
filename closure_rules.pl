
:- multifile r/6.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% 		       Closure Rules
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% closure related to concept subsumption
r(cl_subsumption, 	closure, _, _Lexicon, KB,  
		br([nd( M1, TT1, Args1, true ),
			nd( M2, TT2, Args2, false )
		   ],
		  Sig)
		===>
		br([nd( [], (true, t), [], false )],
		  Sig) ) 
:-
			match_list_ttTerms(Args1, Args2, KB), %!!! why not Args1=Args2?
			once( ( M2 = []
				  %; match_list_only_terms(M1, M2) ) ), 
				  ; subset_only_terms(M2, M1) ) ), % why not subset?
			(%TT1 = TT2; %because features in types
	 			match_ttTerms(TT1, TT2, KB) % ignoring tokens and heads 
	 		; 	ttTerm_to_informative_tt(TT1, (Term1, _Type1)),
				ttTerm_to_informative_tt(TT2, (Term2, _Type2)),
				% not necessary, context defines them of the same time
				%luc(Type1, Type2, _GenType), % mortal:np~>s @ x = mortal:n @ x
	 			%TT1 = (tlp(_,Term1,_,_,_), Type),
	 			%TT2 = (tlp(_,Term2,_,_,_), Type),	
	 			atom(Term1),
				atom(Term2),	 
				isa(Term1, Term2, KB),
				not_disjoint(Term1, Term2, KB) % otherwise weird entailments, as wordnet is too vague
				%Term1 =@= Term2 % no background knowledge
			% for cases when tokens are the same but lemmas are different, % sick-4330
			;   TT1 = (tlp(Tk1,_,_,_,_),_), 
				TT2 = (tlp(Tk2,_,_,_,_),_), 
				isa(Tk1, Tk2, KB),
				not_disjoint(Tk1, Tk2, KB)
	 		%alpha(Norm1, Norm2)
			).

% look at c2 c1 = check c2 c1,  sick-3941, 3938, trot on and ride 5569, 5568
% drawbacks: hunt for -> follow, sick-1133, sick-3050 jump onto -> jump
r(vp_pp_vs_vp, 	closure, _, [[pos('RP')], [pos('IN')], [pos('TO')], [pos('RB')]], KB,  
		br([nd( M1, ( (tlp(_,VP1,_,_,_),_) @ ((tlp(_,_,'IN',_,_),np:_~>pp) @ C, _), Type1 ),   Args1,   true ),
			nd( M2, ( (tlp(_,VP2,_,_,_),_) @ C, Type2 ),   Args2,   false )
		   ],
		  Sig)
		===>
		br([nd( [], (true, t), [], false )],
		  Sig) ) 
:-
			cat_eq(Type1, Type2), % because sick-2388: slice of y: x & slice y: x
			match_list_ttTerms(Args1, Args2, KB),
			once( ( M2 = []
				  ; match_list_only_terms(M1, M2) ) 
				),
	 		atom(VP1), atom(VP2),	 
			isa(VP1, VP2, KB).


% closure related to comlex concept subsumption (dirty addition to cl_subsumption)
r(cl_subsumption_complex, 	closure, _, _Lexicon, KB,  %!!! is this rule worthy to have? check
		br([nd( M1, (TTmod1@TT1, Ty1), Args1, true ),
			nd( M2, (TTmod2@TT2, Ty2), Args2, false )
		   ],
		  Sig)
		===>
		br([nd( [], (true, t), [], false )],
		  Sig) ) 
:-
			luc(Ty1, Ty2, _Type),
			match_list_ttTerms(Args1, Args2, KB),
			once( ( M2 = []
				  ; match_list_only_terms(M1, M2) ) 
				),
			match_ttTerms(TTmod1, TTmod2, KB), % ignoring tokens and heads  !!! no downward monotone e.g. fracas-210
			tt_mon_up(TTmod1), %!!! fracas-211, 210, large mouse-/->large animal
	 		ttTerm_to_informative_tt(TT1, (Term1, _Type1)),
			ttTerm_to_informative_tt(TT2, (Term2, _Type2)),
	 		atom(Term1),
			atom(Term2),	 
			isa(Term1, Term2, KB).


% closure related to "There is"
r(contra_there, 	closure, _, [['there']], _KB,  
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
%sick-trial-1881, sick-train-1358, 1417, 1878, 1884, 3571, 4090, 4094, 4246, 4320, 4329, 6288
r(cl_subcat, 	closure, _, _Lexicon, KB,   
		br([nd( M1, (Tr1, np:_~>TyS1), Args1, true ),  % why not subsumption over Modifiers?
			nd( M2, (Tr2, np:_~>TyS2), Args2, false )
		   ],
		  Sig)
		===>
		br([nd( [], (true, t), [], false )],
		  Sig) ) 
:-
			final_value_of_type(TyS1, s:F1),
			final_value_of_type(TyS2, s:F2),
			once( ( M2 = [] ; match_list_only_terms(M1, M2) ) ),	
			( append(_, Args2, Args1) -> % subcategorization
				( Tr1 =@= Tr2 % avoids matching variable to term, var(X) for variables can slove the global problem
				; %Tr1 = tlp(_,Lm1,Pos1,_,_), Tr2 = tlp(_,Lm2,Pos2,_,_), 
				  %isa(Lm1,Lm2), \+disjoint(Lm1,Lm2,KB), 
				  %\+memberchk('VBN', [Pos1, Pos2])	
				  Tr1 = tlp(_,Lm1,_,_,_), Tr2 = tlp(_,Lm2,_,_,_), 
				  isa(Lm1,Lm2,KB),
				  not_disjoint(Lm1, Lm2, KB), % for sick-4320,4329 but excidental
				  %Lm1 == Lm2,	
				  F1 \= 'pss', F2 \= 'pss'
				)
			; append(Args2, _, Args1), % passivization, maybe constratin S:F=S:pss %sick-3626
			  %Tr1 = tlp(_,Lm1,_,_,_),  % saves sick-4322, 4328
			  %Tr2 = tlp(_,Lm2,'VBN',_,_),
			  %isa(Lm1,Lm2), \+disjoint(Lm1,Lm2,KB) % fails-1756
			  F2 == 'pss',
			  ( Tr1 = tlp(_,Lm1,_,_,_), Tr2 = tlp(_,Lm2,_,_,_), 
				Lm1 == Lm2
			  ; Tr1 =@= Tr2	
			  )	
			), !.

% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% closure about PP-attachment, taken from rules
/* not necessary
r(cl_pp_attach,  closure,  _, _Lexicon,  _KB, % sick-3626, 3657
		br([nd( _,   (P, pp), [C3], true ),
			nd( _M1, (VP1, np:_~>TyS1), Args1, true ), % TLP because M:VP[args] -> M@VP[args] via mods_vp and the rule is applable to M@VP[args] 
			nd(	[M], (VP2, np:_~>TyS2), Args2, false )], 
		  Sig) 
		===>
		br([nd( [], (true, t), [], false )],
		  Sig) ) 
:-
			( VP1=@= VP2; VP1 = tlp(_,Lm,_,_,_), VP2 = tlp(_,Lm,_,_,_) ),  % because tokens can be different
			final_value_of_type(TyS1, s:_),
			final_value_of_type(TyS2, s:_),
			( append(_, Args2, Args1) % subcategorization, 
			; append(Args2, _, Args1) % passivization, maybe constratin S:F=S:pss %sick-3626
			),
			once(( P =.. [tlp|_]; atom(P) )),
			memberchk(C3, Args1),
			ttTerm_to_prettyTerm( (P,_), PrettyP ),
			ttTerm_to_prettyTerm( M, PrettyP ). % simplified, actually M2 should be subset of M1+PrP 
*/


r(cl_ppAtt_fl,  closure,  _, [[ty(pp)]], KB, 
		br([nd( _,   (P, np:_~>pp), [C2,C3], true ),
			nd( _M1, (VP1, np:_~>TyS1), Args1, true ),
			nd(	[M], (VP2, np:_~>TyS2), Args2, false )],    
			%nd(	[], (VP2, np:_~>TyS2), Args2, false )],
		  Sig) 
		===>
		br([nd( [], (true, t), [], false )],
		  Sig) ) 
:-
			( VP1 =@= VP2;   VP1 = tlp(_,Lm1,_,_,_), VP2 = tlp(_,Lm2,_,_,_), isa(Lm1,Lm2,KB) ),  % because tokens can be different, why not isa?
			final_value_of_type(TyS1, s:_),	final_value_of_type(TyS2, s:_),
			( append(_, Args2, Args1) % subcategorization, 
			; append(Args2, _, Args1) % passivization, maybe constratin S:F=S:pss %sick-3626
			),
			once(( P =.. [tlp|_]; atom(P) )),
			memberchk(C3, Args1),
			ttTerm_to_prettyTerm( ((P,_)@C2,_), PrettyP ), 
			ttTerm_to_prettyTerm( M, PrettyP ). % simplified, actually M2 should be subset of M1+PrP 


r(cl_ppConstAtt_fl,  closure,  _, [[ty(pp)]], KB, 
		br([nd( _,   (PP, pp), 			[C3], true ),
			nd( _M1, (VP1, np:_~>TyS1), Args1, true ),
			nd(	[M], (VP2, np:_~>TyS2), Args2, false )],    
			%nd(	[], (VP2, np:_~>TyS2), Args2, false )],
		  Sig) 
		===>
		br([nd( [], (true, t), [], false )],
		  Sig) ) 
:-
			( VP1 =@= VP2;   VP1 = tlp(_,Lm1,_,_,_), VP2 = tlp(_,Lm2,_,_,_), isa(Lm1,Lm2,KB) ),  % because tokens can be different, why not isa?
			final_value_of_type(TyS1, s:_),	final_value_of_type(TyS2, s:_),
			( append(_, Args2, Args1) % subcategorization, 
			; append(Args2, _, Args1) % passivization, maybe constratin S:F=S:pss %sick-3626
			),
			%once(( PP =.. [tlp|_]; atom(PP) )),
			memberchk(C3, Args1),
			ttTerm_to_prettyTerm( (PP,_), PrettyP ), 
			ttTerm_to_prettyTerm( M, PrettyP ). % simplified, actually M2 should be subset of M1+PrP 

% sick-200
r(cl_ppAtt_tr,  closure,  _, [[ty(pp)]], _KB, 
		br([nd( [],    (P, np:_~>pp),    [C,C1], false ),
			nd(	[M|R], (_V, np:_~>TyS),  Args,    true )], 
		  Sig) 
		===>
		br([nd( [], (true, t), [], false )],
		  Sig) ) 
:-			
			final_value_of_type(TyS, s:_),
			memberchk(C1, Args),                    % maybe have a subcategorization rule?
			once(( P =.. [tlp|_]; atom(P) )),
			ttTerm_to_prettyTerm( ((P,_)@C,_), PrettyP ),
			member(Mod, [M|R]), 
			ttTerm_to_prettyTerm( Mod, PrettyP ),
			!.

% sick-9293 aligned
r(cl_ppConstAtt_tr,  closure,  _, [[ty(pp)]], _KB,  
		br([nd( [],    (PP, pp),    	 [C1], false ),
			nd(	[M|R], (_V, np:_~>TyS),  Args,    true )], 
		  Sig) 
		===>
		br([nd( [], (true, t), [], false )],
		  Sig) ) 
:-			
			final_value_of_type(TyS, s:_),
			memberchk(C1, Args),                    % maybe have a subcategorization rule?
			%once(( P =.. [tlp|_]; atom(P) )),
			ttTerm_to_prettyTerm( (PP,_), PrettyP ),
			member(Mod, [M|R]), 
			ttTerm_to_prettyTerm( Mod, PrettyP ).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/*
% closure about Verb particle-arg vs PrepPhrase
% jump over : c1,c2 = not (over c1: jump: c2)
r(cl_vp_pr_arg_pp, 	closure, _, [[pos('RP')], [pos('IN')], [pos('TO')], [pos('RB')]], _KB,   %sick-150
		br([nd( M1, ((tlp(_,Jump,_,_,_), _)@(tlp(_,Over,_,_,_), pr), _), Args1, TF1 ),
			nd( M2, (tlp(_,Jump,_,_,_), _), Args2, TF2 ) % why not isa?
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
			append([P1, [C], P2], Args1),
			append(P1, P2, Args2), !.
*/

% closure related to antonym words
/*r(cl_ant_cnst, 		closure, _, _Lexicon, 
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

r(cl_ant_n_mod, 		closure, _, _Lexicon, KB,  %fracas-204,205
		br([nd( _, ((tlp(_,Lm1,_,_,F1), n:_~>n:_) @ N, n:_), Args, true ),
			nd( _, ((tlp(_,Lm2,_,_,F2), n:_~>n:_) @ N, n:_), Args, true )
		   ],
		  Sig)
		===>
		br([nd( [], (true, t), [], false )],
		  Sig) ) 
:-
			F1 \= 'COL', F2 \= 'COL',
			Lm1 \= Lm2,
			ant_wn(Lm1, Lm2, KB).

/*
% body (of X):Y:False && Lake:Y:True  && Water:X:True  % sick-9631, wrong 338 shows it
% group (of X):Y:True && dog:Y:True  && person:X:True 
r(cl_group_of, 		closure, _,  [['of','group'], ['of','body'], ['of','piece'], ['of','slice'], ['of','crowd'], ['of','bunch'], ['of','herd'], ['of','pair']], KB, 
		br([nd( M, ( (tlp(_,Body,_,_,_),pp~>n:_) @ ((tlp(_,'of',_,_,_),np:_~>pp)@ X, pp), n:_ ), [Y], TF ),
			nd( _, (tlp(_,Water,_,_,_), n:_), [X], true ),
			nd( _, (tlp(_,Lake,_,_,_), n:_),  [Y], true )
		   ],
		  Sig)
		===>
		br([nd( [], (true, t), [], false )],
		  Sig) ) 
:-
			member(Body, ['group', 'body', 'piece', 'slice', 'crowd', 'bunch', 'herd', 'pair']),
			( TF = true ->
				disjoint(Lake, Water)
			; M = [],
			  isa(Lake, Water, KB) 
			).
*/



% C1 did C2, Dance(C2) -> Danced(C1), which problems?
% puting seasoning vs seasoning SICK-5340?? accomodate this too
% make this as a normal rule!

r(cl_do_vp, 	closure, _, [['do']], _KB,  
%r(cl_do_vp, 	closure, _, _Lexicon, _KB,  
		br([nd( M1, (tlp(_,'do',_,_,_), np:_~>np:_~>s:_), 	[C2, C1], 	TF1 ),
		    nd( _, (tlp(_,Dance,_NN,_,_), n:_),				[C2],		TF2 ),
		    nd( M3, (tlp(_,Dance,_,_,_), np:_~>s:_),		[C1],		TF3 )
		   ],
		  Sig)
		===>
		br([nd( [], (true, t), [], false )], % only semnatic terms
		  Sig) ) 
:-
			(	(TF1, TF2, TF3) = (true, true, false), 
             	subset_only_terms(M3, M1) 
			;	(TF1, TF2, TF3) = (false, true, true), 
				subset_only_terms(M1, M3) 
			).
			


% bottle of beer = beer bottle ? protective gear vs gear for protection?
% sick-3275, sick-7477, sick-3373, sick-7755
r(cl_noun_adj_comp, 	closure, _, [[pos('RP')], [pos('IN')], [pos('TO')], [pos('RB')]], KB,  
		br([nd( M1, ((tlp(_,Bottle,_,_,_), pp~>n:_) @ (OF @ C2, pp), n:_), 				[C1], 	TF1 ),
		    nd( _,  (tlp(_,Beer,_,_,_), n:_),											[C2],	TF2 ),
			nd( M3, ((tlp(_,Beerly,_,_,_), n:_~>n:_) @ (tlp(_,Bottle,_,_,_), n:_), n:_), 	[C1],	TF3 )
		   ],
		  Sig)
		===>
		br([nd( [], (true, t), [], false )],
		  Sig) ) 
:-
			OF = (tlp(_,_Of,'IN',_,_), np:_~>pp),	
			once( (Beerly = Beer; derive(Beer, Beerly, KB)) ),
			(	(TF1, TF2, TF3) = (true,  true, false), M3 = [] 
			;	(TF1, TF2, TF3) = (false, true, true),  M1 = []
			).


% closure related to an instance of a predicate
r(cl_instance, 	closure, _,  [[pos('NNP')], [pos('NNPS')]], _KB,  
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


% closure related to concept disjoint
r(cl_disjoint, 	closure, _, _Lexicon, KB,  
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
			Term1 \= Term2,	 
			once( (	disjoint(Term1, Term2, KB),%; % gives weird results with subWN: disjoint(frog,hold), disjoint(reserve,reserve)
					%disjoint_sym(Term1, Term2)	
					not_isa(Term1, Term2, KB), % super strict
					not_isa(Term2, Term1, KB)
				  )
			% antonym?	  	 
			). 


% closure by adjective+noun construction, when compund noun is false
% small animal: c: F, small: c: T, animal: c: T
% small animal: c: T, small: c: F, animal: c: T, sich-7466
% sick-2791
r(cl_adj_noun_1, 	closure, _, _Lexicon,  _KB, 
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
% +for faracs 218 but -for 219 %!!! this makes all adjective intersective!!!
/*
r(cl_adj_noun_2, 	closure, _, _Lexicon, _KB,  
		br([nd( _, ((TLP_adj1, n:_~>n:_) @ TTn, n:_), Args, true ), %non-empty modlist
			nd( _, TTn, Args, true ),
			nd( [], (TLP_adj2, np:_~>s:_), Args, false )
		   ],
		  Sig)
		===>
		br([nd( [], (true, t), [], false )],
		  Sig) ) 
:-
			%fail, 
			TLP_adj1 = tlp(_,Adj,_,_,_),
			TLP_adj2 = tlp(_,Adj,_,_,_). 
*/

% closure rule about exactly_N, why not as an lexical knowledge?
% fracas-85

r(cl_exact_num, 	closure, _, [['exactly'], ['just']], _KB,  
		br([nd( _, ((((TLP_RB, (n:_~>(np:_~>s:_)~>s:_)~>n:_~>(np:_~>s:_)~>s:_) @ TT_CD1, _) @ TTn, _) @ TTvp, s:_),  Args, true ),
			nd( _, (((tlp(_,Lm2,POS2,_,_), n:_~>(np:_~>s:_)~>s:_) @ TTn, _) @ TTvp, s:_), Args, true )
		   ],
		  Sig)
		===>
		br([nd( [], (true, t), [], false )],
		  Sig) ) 
:-
			member(POS2, ['DT', 'CD']), % a_few=DT, one=CD
			TLP_RB = tlp(_,Lm_RB,_,_,_),
			TT_CD1 = (tlp(_,Lm1,POS1,_,_), n:_~>(np:_~>s:_)~>s:_), 
			member(POS1, ['DT', 'CD']), %frac-299
			member(Lm_RB, ['exactly', 'just']),
			is_greater(Lm2, Lm1).


% closure for  {"c wears a/s white cloth"=F, "d is white"=T, "c is in d"=T}
% not true     {"c wears a/s white cloth"=T, "d is white"=T, "c is in d"=F} 
%!!!but we allow both cases and it is interesting what type of unsoundness it will evoke
% sick-218, sick-9136
r(cl_wear_cloth, 	closure, _, [['wear']], _KB,  
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
			( TT_Cloth1 = ((tlp(_,Cloth2,_,_,_COL),_) @ (tlp(_,Cloth,_,_,_),n:_), n:_), %sick-218
			  ( once(member(Cloth, ['cloth', 'clothes']))
			  ; word_hyp(Cloth, 'clothing', _) %relaxing constraints
			  )
			; 
			  TT_Cloth1 = (tlp(_,Cloth2,_,_,_), _), %sick-9136
			  word_hyp(Cloth2, 'clothing', _)
			).
			  
% euqlity rule for closure
			  
r(cl_equal, 	closure, _, [['be']], _KB,  
		br([nd( [], (tlp(_,'be',_,_,_), np:_~>np:_~>s:_),  [A, A], false )],
		  Sig)
		===>
		br([nd( [], (true, t), [], false )],
		  Sig) ) 
:-
			true.
			







