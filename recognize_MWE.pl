%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Recognizing MultiWord Expressions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

clean_ccgTerm_once(Term, Clean1) :- 
	loc_fix_ccgTerm(Term, Clean), 
	cf_annotation(Clean, Clean1),
	!.




loc_fix_ccgTerm((TC_term, Cat), Clean) :-
	var(TC_term),
	Clean = (TC_term, Cat).

loc_fix_ccgTerm(App_TC, Fixed) :-
	once(detect_mwe(App_TC, PreFixed)),
	( debMode('mwe') -> report(['!!! MWE detected', PreFixed]); true ),
  	loc_fix_ccgTerm(PreFixed, Fixed). 

loc_fix_ccgTerm(App_TC, Fixed) :-
	App_TC = (_@_, Cat),
	remove_pp_arg(App_TC, App_TC2),
	App_TC2 = (TC1@TC2, Cat), 
  	loc_fix_ccgTerm(TC1, Clean1),
  	loc_fix_ccgTerm(TC2, Clean2),
	Fixed = (Clean1 @ Clean2, Cat). 

loc_fix_ccgTerm((TC_term, Cat), Clean) :-
	TC_term = abst(X, SubTC), 
	Clean = (abst(X, SubClean), Cat), 
	loc_fix_ccgTerm(SubTC, SubClean).

loc_fix_ccgTerm((TC_term, Cat), Clean) :-
	TC_term = (_, _),
	loc_fix_ccgTerm(TC_term, Clean1),
	Clean = (Clean1, Cat). 

loc_fix_ccgTerm(TC, TC). 





detect_mwe(App_TC, Fixed) :-
	mwe_take_part_in(App_TC, Fixed);
	mwe_at_least(App_TC, Fixed);
	mwe_a_few(App_TC, Fixed);
	mwe_because_of(App_TC, Fixed);
	%mwe_give_up(App_TC, Fixed); %makes difficult to analyses wrong parses
	n_mod_to_arg_pp(App_TC, Fixed);
	mwe_a_lot_of_n(App_TC, Fixed);
	%Fixed = App_TC.
	fail.


% take @ (part @ (in @ NP, pp), np) : np~>s ~~~~> take_part_in @ NP %!!! wrong, do only take_part
% but not "spend time at"
mwe_take_part_in( ((Take,_) @ ((Part,_) @ ((In,_) @ TTnp, pp), np:_), np:F1~>s:F2), Fixed) :- 
	TTnp = (_, np:_),
	nonvar(Take), 
	Take = tlp(Tk1,Lm1,POS,Feat1,Feat2),
	member(Lm1, ['take']),
	atom_chars(POS, ['V','B'|_]),  
	nonvar(Part), 
	Part = tlp(Tk2,Lm2,_,_,_),
	nonvar(In),   
	In = tlp(Tk3,Lm3,'IN',_,_),
	atomic_list_concat([Tk1,'_',Tk2,'_',Tk3], Token),
	atomic_list_concat([Lm1,'_',Lm2,'_',Lm3], Lemma),
	Fixed = ( (tlp(Token,Lemma,POS,Feat1,Feat2), np:_~>np:F1~>s:F2) @ TTnp, np:F1~>s:F2).

% (take @ (part)) @ (in @ NP, pp) : np~>s ~~~~> take_part_in @ NP
mwe_take_part_in( (((Take,_) @ PartNP,_) @ ((In,_) @ TTnp, pp), np:F1~>s:F2), Fixed) :- 
	TTnp = (_, np:_),
	nonvar(Take), 
	Take = tlp(Tk1,Lm1,POS,Feat1,Feat2),
	member(Lm1, ['take']),
	atom_chars(POS, ['V','B'|_]),  
	nonvar(PartNP), 
	unpack_ttTerm(PartNP, (tlp(Tk2,Lm2,_,_,_),_)),
	nonvar(In),   
	In = tlp(Tk3,Lm3,'IN',_,_),
	atomic_list_concat([Tk1,'_',Tk2,'_',Tk3], Token),
	atomic_list_concat([Lm1,'_',Lm2,'_',Lm3], Lemma),
	Fixed = ( (tlp(Token,Lemma,POS,Feat1,Feat2), np:_~>np:F1~>s:F2) @ TTnp, np:F1~>s:F2).

 
% at @ least : s~>s
mwe_at_least( ((tlp(_,'at',_,_,_),_) @ (tlp(_,'least',POS,Feat1,Feat2),_), s:F1~>s:F2), Fixed) :- 
	Fixed = (tlp('at_least','at_least',POS,Feat1,Feat2), s:F1~>s:F2). 
	 
% a few
mwe_a_few(((TLP_a, n:F1~>np:F2) @ (TC_few @ TCn, n:F1), np:F2), Fixed) :-
	TLP_a = tlp(_, 'a', POS, Feat1, Feat2),
	TC_few = (tlp(_,'few',_,_,_), n:_~>n:_),
	TC_a_few = (tlp('a_few', 'a_few', POS, Feat1, Feat2), n:F1~>np:F2),
	Fixed = (TC_a_few @ TCn, np:F2).

% more than one -> more_than_one, CD
%mwe_more_than_one((((Than_TLP, _) @ (More_TLP, _), (n:_~>n:_)~>n:_~>n:_) @ (tlp(_,Num,'CD',_,_), _), _), Fixed) :-
%	nonvar(Num),
%	nonvar(Than_TLP), Than_TLP = tlp(_,'than',_,_,_),
%	nonvar(More_TLP), More_TLP = tlp(_,'more',_,_,_),
%	Fixed = (TC_a_few @ TCn, np:F2).
	

% because of, according to, prior to, back to, regardless of, along with
mwe_because_of((TC1 @ TC2, Cat), Fixed) :- % cat stays unchanged
	TC1 = (tlp(Token1, Lemma1, POS, Feat1, Feat2), pp~>Cat),
	Cat = (np~>s:dcl)~>np~>s:dcl,
	TC2 = (TC2_1 @ TC2_2, pp),
	TC2_1 = (tlp(Token2, Lemma2, _,_,_), np~>pp),
	atomic_list_concat([Token1, '_', Token2], Token),
	atomic_list_concat([Lemma1, '_', Lemma2], Lemma),	
	Fixed = ( (tlp(Token, Lemma, POS, Feat1, Feat2), np~>Cat) @ TC2_2 , Cat). 

% carry out, give up, come out, set up, sit down, paid out, lock out, take over
mwe_give_up((TC1 @ TC2, Cat), Fixed) :-  % cat stays unchanged
	TC1 = (tlp(Token1, Lemma1, POS, Feat1, Feat2), pr~>Cat),
	TC2 = (tlp(Token2, Lemma2, _,_,_), pr),
	atomic_list_concat([Token1, '_', Token2], Token),
	atomic_list_concat([Lemma1, '_', Lemma2], Lemma),
	Fixed = (tlp(Token, Lemma, POS, Feat1, Feat2), Cat).


% a lot of ((_,n), np)  ---> a_lot_of (_,n)
mwe_a_lot_of_n( (TTa @ (TTlot @ (TTof @ TTHead, pp), n:_), np:F1), Fixed) :-
	TTa = (tlp(_,'a',_,_,_), _),
	TTlot = (tlp(_,'lot',_,_,_), _),
	TTof = (tlp(_,'of',_,_,_), _),
	TTalotof = (tlp('a_lot_of','a_lot_of','DT','0','Ins'), n:F2~>np:F1), 
	( 	TTHead = ((Noun, n:F2), np:_) ->
			TTnoun = (Noun, n:F2)
		; TTHead = (_, n:F2) ->
			TTnoun = TTHead
		; 	writeln('Problem with a head of a_lot_of'),  %sick-8892 a lot of (blooming trees, vp)
		 	fail	   
	),
	Fixed = (TTalotof @ TTnoun, np:F1).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% corrects pp that is vp modifier but attached to the vp argument
% spend ( a ((at home) (lot of time)) ) ---> spend (a (lot of time), (at home)) 
n_mod_to_arg_pp( (TTvp @ (TTa @ (TTn_mod @ TTn, n:_), np:F2), np:F3~>s:F4),  Fixed ) :-
	nonvar(TTn), nonvar(TTa),
	TTn = ( (tlp(_,'lot',_,_,_),pp~>n:_) @ _TTpp, n:_),
	TTn_mod = (_, n:_~>n:_),
	%TTvp = (tlp(_,_,_,_,_), np:_~>np:_~>s:_), % lets ignire first
	set_type_for_tt(TTn_mod, pp, TTarg_pp),
	set_type_for_tt(TTvp, np:F2~>pp~>np:F3~>s:F4, NewTTvp),
	Fixed = ( (NewTTvp @ (TTa @ TTn, np:F2), pp~>np:F3~>s:F4) @ TTarg_pp, np:F3~>s:F4 ). 


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
remove_pp_arg( ((Exp, Cat) @ TC, np:F2), Fixed_TC) :-
	Cat = (pp~>n:F1)~>np:F2,
	TC = (ArgExp, pp~>n:F1),
	New_Cat = n:F1~>np:F2,
	nonvar(ArgExp),
	( Exp = tlp(_,_,'PRP$',_,_),
	  	TCfun = (Exp, New_Cat);  
	  Exp = (TLP, C2~>Cat) @ TC2,
		TLP = tlp('\'s',_,_,_,_),
		TCfun = ((TLP, C2~>New_Cat) @ TC2, New_Cat) ), !,
	( ArgExp = abst(X, TC1) ->
		del_var_pp(X, TC1, New_TC);
		remove_pp_type_from_tt(TC, New_TC) ), 	
	New_TC = (_, n:F1),
	Fixed_TC = (TCfun @ New_TC, np:F2). 
	
remove_pp_arg(A, A).
	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% delete only variable TC:pp
del_var_pp( TC_X, ( (Exp, pp~>n:F) @ (X,pp), n:F ), New_TC ) :-
	TC_X == (X, pp), !,
	set_type_for_tt( (Exp, pp~>n:F), n:F, New_TC),
	New_TC = (_, n:F).

del_var_pp( TC_X, (TC1_Fun @ TC1_Arg, Cat), (TC2_Fun @ TC2_Arg, Cat) ) :-
	!, del_var_pp(TC_X, TC1_Fun, TC2_Fun),
	del_var_pp(TC_X, TC1_Arg, TC2_Arg).	

del_var_pp( _, (tlp(Tk,Lm,P,F1,F2),Cat), (tlp(Tk,Lm,P,F1,F2),Cat) ).
	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Remove type pp
remove_pp_type_from_tt( (Term, Type), (Term, NewType) ) :- 
	(	var(Term); 
		Term =.. [tlp | _] ), !,
	remove_type_from_type(Type, pp, NewType).

remove_pp_type_from_tt( (TT1 @ TT2, _), ((T1,Ty2~>Ty1)@(T2,Ty2), Ty1) ) :-
	!, remove_pp_type_from_tt( TT1, (T1,Ty2~>Ty1) ),
	remove_pp_type_from_tt( TT2, (T2,Ty2) ).

remove_pp_type_from_tt( ((Exp, Ty), TyPP), ((Exp, Ty), Type) ) :-
	remove_type_from_type(TyPP, pp, Type).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% removes pp from type, except the case when
% pp is the only type or a value type
remove_type_from_type(Type, _, Type) :-
	\+ Type =.. ['~>' | _], !.
	
remove_type_from_type(A~>B, Remove, Type) :-
	subsumes_term(Remove, A), !,
	remove_type_from_type(B, Remove, Type).

remove_type_from_type((A~>B)~>C, Remove, Type1~>Type2) :-
	remove_type_from_type(A~>B, Remove, Type1),
	remove_type_from_type(C, Remove, Type2).


	





