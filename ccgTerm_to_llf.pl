%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% beginings of ccgTree to LLF convertion
ccgTerm_to_llf(Term_H, LLF) :-
	once(clean(Term_H, LLF)).
	


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Cleans CCG_term by applying clean_list 
clean(X,_) :-	var(X), writeln('Variable accounted'), !, fail.

clean( (X,Ty,H), (X,Ty,H) ) :-
	var(X), !.

clean( A, B) :-
	once(clean_list(A, C)),
	clean(C, B).
	
clean( (A@B,Ty,H), (A1@B1,Ty,H) ) :-
	clean(A, A1),
	clean(B, B1).

clean( (abst(A,B),Ty,H), (abst(A1,B1),Ty,H) ) :-
	clean(A, A1),
	clean(B, B1).

clean( ((A,Ty1,H),Ty2,H), ((A1,Ty1,H),Ty2,H) ) :-
	clean( (A,Ty1,H), (A1,Ty1,H) ).

clean( A, A ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
clean_list(A, B) :-
	% lex_rule (A conj B) -> conj (lex_rule A) (lex_rule B)
	put_lex_rule_under_conj(A, B); % takes scope over others
	% plural the to s-morpheme
	the_nns_to_s_nns(A, B);
	% plural some to several
	some_nns_to_afew_nns(A, B);
	% two of NNS ---> two NNS
	numOfNNS_to_numNNS(A, B);
	% cat1=n, cat2=np, cat(Quant:JJ)=n~>n to (Quant, n~>np) @ n
	nn_to_n_np(A, B);
	%tlp NNP of cat1=n, cat2=np convert to tlp of cat=np 
	nnp_n_np_to_np(A, B); 
	%tlp NN of cat1=n, cat2=np convert to tlp of cat=np 
	nn_n_np_to_np(A, B);
	%tlp NNS of cat1=n, cat2=np convert to tlp of cat=np 
	nns_n_np_to_np(A, B);
	%tt of cat1=n, cat2=np convert to tt of cat=np 
	n_np_to_np(A, B);
	np_pss_to_n_n(A, B);
	% (owning X) (every man) --> who (owning X) (every man)
	lex_rule_np_s_to_np_np(A, B);
	%nnp_conj_n_np_to_np(A, B); % canceled by put_lex_rule_under_conj
	put_mod_inside_who(A, B);
	comma_to_and(A, B);
	attach_remote_DT_to_noun(A, B);
	n_mod_everyone(A, B);
	some_one(A, B); %sick-2405, 6146, 3258
	some_sleeping_one(A, B); %sick-2404
	% relative clause should modify noun not np
	put_rel_cl_under_det(A, B);
	% put pp modifier under det and attached to noun
	put_ppMod_under_det(A, B); 
	% inserts which:vp,np,np as np modifier (for wrong analyses mainly)
	np_which_mod(A, B);
	% all the dogs ---> all dogs
	pdt_rm_dt_noun(A, B);
	% poss_pr to pos@pr
	poss_pr_to_s_pr(A, B);
	% not (all dogs) ---> not all dogs
	not_all_NN(A, B);
	% not everybody ---> not every person
	not_everybody(A, B);
	%nn_n(A, B);
	%it_is_np(A, B);
	%it_is_mod(A, B);
	fail.


% lex_rule (A conj B) -> conj (lex_rule A) (lex_rule B)
put_lex_rule_under_conj( ((TTexp, Ty1, _H1), Ty2, _H2),  New_X ) :-
	TTexp = (Conj @ TT1, Ty1~>Ty1, _) @ TT2,
	Conj = (tlp(Tk,Lm,POS,F1,F2), Ty~>Ty~>Ty, _),
	New_Type = Ty2~>Ty2~>Ty2,
	New_Conj = (tlp(Tk,Lm,POS,F1,F2), New_Type, H_Conj),
	H_Conj = tlp(New_Type,Lm,POS,F1,F2),
	TT1 = (_, _, H_TT1),
	TT2 = (_, _, H_TT2),
	New_TT1 = (TT1, Ty2, H_TT1),
	New_TT2 = (TT2, Ty2, H_TT2),
	( debMode('fix') -> report(['!!! Fix: put_lex_rule_under_conj']); true ),
	New_X = ((New_Conj @ New_TT1, Ty2~>Ty2, H_Conj) @ New_TT2, Ty2, H_TT2). 


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% e.g. who (a woman) sleeps ---> a (who woman sleep)
% sick-2722
put_rel_cl_under_det( (WhTTH @ (QuanTTH@NounTTH,np:_,H_Quant), np:_, _), Fixed) :-
	WhTTH = ((tlp(Tk,Lm,POS,Feat1,Feat2), VpTy~>np:_~>np:_, _) @ VP , np:_~>np:_, _),
	QuanTTH = (tlp(_,_,'DT',_,_), n:_~>np:_, H_Quant), 
	nonvar(POS),
	member(POS, ['WDT', 'WP']),
	New_Head_Wh = tlp(VpTy~>n:_~>n:_, Lm, POS, Feat1, Feat2), 
	New_WhTTH = ((tlp(Tk,Lm,POS,Feat1,Feat2), VpTy~>n:_~>n:_, New_Head_Wh) @ VP, n:_~>n:_, New_Head_Wh),
	( debMode('fix') -> report(['!!! Fix: put_rel_cl_under_det']); true ),
	Fixed = (QuanTTH @ (New_WhTTH @ NounTTH, n:_, New_Head_Wh), np:_, H_Quant). 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% e.g. (of:np,np,np) (s friend) (a group) ---> a ((of:np,n,n) (s friends) group)
% sick-140 eccg
put_ppMod_under_det( (((Of,np:_~>np:_~>np:_,_)@NP1,np:_~>np:_,_) @ NP2, np:_, _), Fixed) :-
	clean(NP2, (Det@N,np:_,HDet)),
	Of = tlp(_,Lm,'IN',F1,F2),
	TypeOf = np:_~>n:_~>n:_,
	HOf = tlp(TypeOf, Lm, 'IN', F1, F2),
	NewOf = (Of, TypeOf, HOf),
	NewPP = (NewOf @ NP1, n:_~>n:_, HOf),
	N = (_,n:_,HN),
	Det = (_,n:_~>np:_,HDet),
	( debMode('fix') -> report(['!!! Fix: put_ppMod_under_det']); true ),
	Fixed = (Det @ (NewPP@N,n:_,HN), np:_, HDet). 


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% e.g. Oracle,NNP,n -> np -----> Oracle,NNP,np
% something, everybody, 'DT'
% Jews, Americans, States, Airlines, 'NNPS'
% it,PRP; then,RB; more,JJR  n -> np --------> X,PRP,np
nnp_n_np_to_np( (X, np:_, _),  (tlp(Token,Lemma,POS,F1,F2), np:_, H1) ) :-
	X = (tlp(Token,Lemma,POS,F1,F2), n:_, _),
	(POS = 'NNP'; POS = 'DT'; POS = 'NNPS'; POS = 'PRP'; POS = 'RB'; POS = 'JJR'),
	( debMode('fix') -> report(['!!! Fix: proper names as np']); true ),
	H1 = tlp(np:_,Lemma,POS,F1,F2).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% e.g. and@(X,n)@(Y,n) : n -> np -----> and@(X,n,np)@(Y,n,np) : np
/* % canceled by put_lex_rule_under_conj
nnp_conj_n_np_to_np( (X, np:_, _),  New_X ) :- 
	X = ( (Conj@TT1, Ty~>Ty, _) @ TT2, n:_, _),
	Conj = (tlp(Tk,Lm,POS,F1,F2), Ty~>Ty~>Ty, _),
	New_Type = np:_~>np:_~>np:_,
	New_Conj = (tlp(Tk,Lm,POS,F1,F2), New_Type, H_Conj),
	H_Conj = tlp(New_Type,Lm,POS,F1,F2),
	New_TT1 = (TT1, np:_, _),
	New_TT2 = (TT2, np:_, _),
	( debMode('fix') -> report(['!!! Fix: conj n n to conj np np']); true ),
	New_X = ((New_Conj @ New_TT1, np:_~>np:_, _) @ New_TT2, np:_, _). 
*/	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% n with NN heads to np
% e.g. oil,NN,n -> np -----> a@oil,DT,np
nn_n_np_to_np( (X, np:_, _),  (Y @ X, np:_, H_Y) ) :-
	X = (tlp(_,_,'NN',_,_), n:_, _),
	( debMode('the') -> 
		Y = (tlp('the','the','DT','I-NP','Ins'), n:_~>np:_, H_Y),
		H_Y = tlp(n:_~>np:_,'the','DT','I-NP','Ins')
	  ; Y = (tlp('a','a','DT','I-NP','Ins'), n:_~>np:_, H_Y),
		H_Y = tlp(n:_~>np:_,'a','DT','I-NP','Ins')
	),
	( debMode('fix') -> report(['!!! Fix: insert DT for n:NN constant']); true ).

/*nn_n_np_to_np( (X, np:F, _),  (New_X, np:F, H) ) :- % version 2, all matching nouns are constants
	X = (tlp(Tk,Lm,'NN',F1,F2), n:_, _),
	New_X = tlp(Tk,Lm,'NN',F1,F2),
	H = tlp(np:F,Lm,'NN',F1,F2).
	*/

% e.g. crude@oil,NN,n ------> a@(cruid@oil),DT,np
% e.g. oil,NN,pp~>n for april delivery ----> a@(oil@for_april_delivery)
nn_n_np_to_np( (X, np:_, _),  (Y @ X, np:_, H_Y) ) :-
	X = (_, n:_, H),
	nonvar(H),	
	H = tlp(Cat,_,'NN',_,_),
	(Cat = n:_; Cat = pp~>n:_),
	( debMode('the') -> 
		Y = (tlp('the','the','DT','I-NP','Ins'), n:_~>np:_, H_Y),
		H_Y = tlp(n:_~>np:_,'the','DT','I-NP','Ins')
	  ; Y = (tlp('a','a','DT','I-NP','Ins'), n:_~>np:_, H_Y),
		H_Y = tlp(n:_~>np:_,'a','DT','I-NP','Ins')
	),
	( debMode('fix') -> report(['!!! Fix: insert DT for n:NN complex term']); true ).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ((((M,np~>s),n~>n) @ Smith:n:NNP, n), np) --->  (which:(np~>s)~>np~>np @ M:np~>s) @ Smith:np
% Smith see X did Y, wrong analysis mainly, fracas-345
np_which_mod(  ((((VP, np:_~>s:_, H_VP), n:_~>n:_, _) @ (N, n:_, _), n:_, _), np:_, _), New_TTH) :-
	N = tlp(_Tk, Lm, POS, F1, F2),
	H_NNP = tlp(np:_, Lm, POS, F1, F2), 
	TTH_NNP = (N, np:_, H_NNP), 
	Cat_Wh = (np:_~>s:_)~>np:_~>np:_,
	H_Wh = tlp(Cat_Wh,'which','WDT','I-NP','Ins'),
	Which = (tlp('which','which','WDT','I-NP','Ins'), Cat_Wh, H_Wh),
	( debMode('fix') -> report(['!!! Fix: insert Which:vp,np,np for modifying np']); true ),  
	New_TTH = ((Which @ (VP, np:_~>s:_, H_VP), np:_~>np:_, H_Wh) @ TTH_NNP, np:_, H_NNP).  



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% n with NNS heads to np, NNS is changed in NN by simply/2 predicate
% e.g. dogs,NNS,n -> np -----> s@dogs,PL,np
nns_n_np_to_np( (X, np:_, _),  (Y @ X, np:_, H_Y) ) :-
	X = (tlp(_,_,'NNS',_,_), n:_, _),
	( debMode('the') -> 
		Y = (tlp('the','the','DT','0','Ins'), n:_~>np:_, H_Y),
		H_Y = tlp(n:_~>np:_,'the','DT','0','Ins')
	  ; Y = (tlp('s','s','DT','0','Ins'), n:_~>np:_, H_Y), 
		H_Y = tlp(n:_~>np:_,'s','DT','0','Ins')
	),
	( debMode('fix') -> report(['!!! Fix: insert DT for n:NNS constant']); true ).
	%Y = (tlp('s','s','DT','0','Ins'), n:_~>np:_, H_Y)
	%Y = (tlp('a','a','DT','I-NP','O'), n~>np),
	%H_Y = tlp(n:_~>np:_,'s','DT','0','Ins').
% e.g. hungry@dogs,NNS,n -> np -----> s@(hungry@dogs),PL,np
% e.g. apples,NNS,pp~>n for april delivery ----> a@(apples@for_april_delivery)
nns_n_np_to_np( (X, np:_, _),  (Y @ X, np:_, H_Y) ) :-
	X = (_, n:_, H),
	nonvar(H),	
	H = tlp(Cat,_,'NNS',_,_),
	( Cat = n:_; Cat = pp~>n:_),
	( debMode('the') -> 
		Y = (tlp('the','the','DT','0','Ins'), n:_~>np:_, H_Y),
		H_Y = tlp(n:_~>np:_,'the','DT','0','Ins')
	  ; Y = (tlp('s','s','DT','0','Ins'), n:_~>np:_, H_Y), 
		H_Y = tlp(n:_~>np:_,'s','DT','0','Ins')
	),
	( debMode('fix') -> report(['!!! Fix: insert DT for n:NNS complex term']); true ). 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% type change from n to np
% e.g. $@37,CD,n:num -> np -----> $@37,CD,np
n_np_to_np( (X, np:_, _),  New_TTH ) :-
	X = (TLP, n:_, H),
	nonvar(TLP),
	TLP =.. [tlp | _],
	nonvar(H),
	H = tlp(n:num,Lm,'CD',F1,F2),
	( atom_chars(F2, [_,_,'D','A','T']) -> 
 		Feat = 'dat'
	  ;	Feat = 'num'
	),
	%Y = (tlp('the','the','DT','I-NP','Ins'), n:_~>np:_, H_Y),  
	%H_Y = tlp(n:_~>np:_,'the','DT','I-NP','Ins'),
	%New_TTH = (Y @ X, np:_, H_Y).
	New_TTH = (TLP, np:Feat, tlp(np:Feat,Lm,'CD',F1,F2)). 

% a girl in (white, n, np)	
n_np_to_np( (X, np:_, _),  (Y @ X, np:_, H_Y) ) :-
	X = (tlp(_,_,'JJ',_,_), n:_, _H),
	( debMode('the') ->
		Y = (tlp('the','the','DT','I-NP','Ins'), n:_~>np:_, H_Y),
		H_Y = tlp(n:_~>np:_,'the','DT','I-NP','Ins')
	  ; Y = (tlp('a','a','DT','I-NP','Ins'), n:_~>np:_, H_Y),
		H_Y = tlp(n:_~>np:_,'a','DT','I-NP','Ins')
	),
	( debMode('fix') -> report(['!!! Fix: insert DT for n:JJ constants']); true ). 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% X:np->s:pss/ng  -> n->n  ------>  which @ (is @ X)  
% e.g. from@Canada@produced,np->s:pss -> n->n -----> which@(is@(from@Canada@produced))
np_pss_to_n_n( ((X, Cat_X, H_X), n:_~>n:_, _), (Which @ Is_X, n:_~>n:_, H_Which) ) :- %!!! how do you deal with the verb then? any rule fpr this?
	Cat_X = np:_~>s:F,
	memberchk(F, [ng, adj, pss, dcl]), % adj: full of X:np~>s:sdj--->n~>n  
	% define which
	Cat_Which = (np:_~>s:dcl)~>n:_~>n:_,
	H_Which = tlp(Cat_Which,'which','WDT','I-NP','Ins'),
	Which = (tlp('which','which','WDT','I-NP','Ins'), Cat_Which, H_Which),  
	% define is
	Cat_Is = Cat_X~>np:_~>s:dcl,
	H_Is = tlp(Cat_Is,'be','VBZ','I-VP','Ins'),
	Is = (tlp('is','be','VBZ','I-VP','Ins'), Cat_Is, H_Is),
	( debMode('fix') -> report(['!!! Fix: insert Which Is for lex_rule']); true ),
	Is_X = (Is @ (X, Cat_X, H_X), np:_~>s:dcl, H_X).


% for ((owning cars) (evevry man)) -> ( who (owning cars) (evevry man))
lex_rule_np_s_to_np_np( ( ((VP,np:A~>s:B,H1), np:C~>np:D, _) @ DetNP, np:E, H3), New ) :- 
	% define NP modifier "who", we dont use "is"
	Cat_Wh = (np:A~>s:B)~>np:C~>np:_,
	H_Wh = tlp(Cat_Wh,'who','WDT','I-NP','Ins'),
	Wh = (tlp('who','who','WDT','I-NP','Ins'), Cat_Wh, H_Wh), 
	% define is
	Cat_Is = (np:A~>s:B)~>np:A~>s:B,
	H_Is = tlp(Cat_Is,'be','VBZ','I-VP','Ins'),
	Is = (tlp('is','be','VBZ','I-VP','Ins'), Cat_Is, H_Is), 
	Be_VP = (Is @ (VP,np:A~>s:B,H1), np:A~>s:B, H1),
	( debMode('fix') -> report(['!!! Fix: insert Which Is for lex_rule']); true ),
	New = ( (Wh @ Be_VP, np:C~>np:D, H_Wh) @ DetNP, np:E, H3 ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% attach the modifier to the head of rlative clause or passive clause
% (X, n~>n) @ [(who @ Z, n~>n) @ (Y,n)] ~~~> (who @ Z, n~>n) @ [(X, n~>n) @ (Y,n)] 
% (X, n~>n) @ [((VPpass:np~>s), n~>n) @ (Y,n)] ~~~>((VPpass:np~>s), n~>n) @ [(X, n~>n) @ (Y,n)]  %sick-2712, 7649
put_mod_inside_who( (TTn_mod @ (TTwho_nn @ TTn, n:_, _H1), n:_, _H2), New ) :-
	nonvar(TTwho_nn),
	( TTwho_nn = ((tlp(_,'who',_,_,_),_,_) @ _TTvp, n:_~>n:_, _H)
	; TTwho_nn = ( (_, np:_~>s:_, _), n:_~>n:_, _)	
	),
	TTn_mod = (TTexp, _~>N, _),
	TTexp \= (_,_,_), % "posed slept man" will loop in commutation modifiers, sick-964
	TTn = (_, _, Hn),	
		( debMode('fix') -> report(['!!! Fix: put_mod_inside_who']); true ),
	New = (TTwho_nn @ (TTn_mod @ TTn, N, Hn), N, Hn).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% change type n~>n to n~>np for JJ(S) words like many, several, most, few, etc
nn_to_n_np( (((TLP,n:F1~>n:_,_) @ TTn,n:_,_), np:F2,_), ((NewTLP,Ty,H) @ TTn, np:F2, H) ) :-
	TLP = tlp(Tk,Lem,Pos,Feat1,Feat2),
	Ty = n:F1~>np:F2,
	( member(Lem, ['several', 'many', 'few', 'most']) ->
		NewPos = 'DT'
	  ; Pos = 'CD',
		NewPos = Pos 
	),	
	H = tlp(Ty, Lem, NewPos, Feat1, Feat2),   %!!! Check that this takes ito account plural cases too: several dogs
	( debMode('fix') -> report(['!!! Fix: identify modifiers as quantifiers']); true ), 
	NewTLP = tlp(Tk, Lem, NewPos, Feat1, Feat2).
% exactly,(n~>n)~>n~>n @ two,n~>n @ N,n : np ~~~> exactly,(n~>np)~>n~>np @ two,n~>np @ N,n - fracas-85 
nn_to_n_np( (((TTexp,n:F1~>n:_,_) @ TTn,n:_,_), np:F2,_), ((NewTLP,Ty,H_CD) @ TTn, np:F2, H_CD) ) :-
	TTexp = (TLP_RB, (n:_~>n:_)~>n:_~>n:_, _) @ (TLP_CD, n:_~>n:_, _),
	TLP_RB = tlp(_,Lm1,'RB',Feat11,Feat12),
	TLP_CD = tlp(_,Lm2,'CD',Feat21,Feat22),
	Ty = n:F1~>np:F2,
	H_RB = tlp(Ty~>Ty,Lm1,'RB',Feat11,Feat12),
	H_CD = tlp(Ty,Lm2,'CD',Feat21,Feat22), 
	( debMode('fix') -> report(['!!! Fix: change type to correct one']); true ),
	NewTLP = (TLP_RB, Ty~>Ty, H_RB) @ (TLP_CD, Ty, H_CD).
	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Change plural-some to several
some_nns_to_afew_nns( ((Some,n:F1~>np:F2,_) @ TTn,np:F3,_), ((Afew,Ty,H) @ TTn, np:F3, H) ) :-
	Some = tlp(_, Lem, 'DT', _Feat1, _Feat2),
	TTn = (_, _, tlp(_,_,'NNS',_,_)),
	member(Lem, ['some']), 
	Ty = n:F1~>np:F2, 
	Afew = tlp('a_few','a_few','DT','0','Ins'),
	H = tlp(Ty,'a_few','DT','0','Ins').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Change plural-the to s-morpehem 
the_nns_to_s_nns( ((The,n:F1~>np:F2,TheH) @ TTn,np:F3,_), ((S_DT,Ty,H) @ TTn, np:F3, H) ) :-
	The = tlp(_, Lem, 'DT', _Feat1, Feat2), 
	Feat2 \= 'VIP', % avoids a loop
	TTn = (_, _, tlp(_,_,'NNS',_,_)),
	member(Lem, ['the']), % different from several, some
	Ty = n:F1~>np:F2, 
	( debMode('the') ->
		S_DT = The, Feat2 = 'VIP',
		H = TheH
	  ; S_DT = tlp('s','s','DT','0','Ins'),
		H = tlp(Ty,'s','DT','0','Ins')
	).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% change conjunctive comma to and
comma_to_and( (tlp(',', ',', ',', F1, F2), Ty~>Ty~>Ty, _), (TLP, Ty~>Ty~>Ty, NewH) ) :-
	TLP = tlp('and', 'and', 'CC', F1, F2),
	( debMode('fix') -> report(['!!! Fix: comma replaced by and']); true ),
	NewH = tlp(Ty~>Ty~>Ty, 'and', 'CC', F1, F2).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% attach remote DT to the head of NP
% e.g. The [people who were at the meeting] [All] laughed 
attach_remote_DT_to_noun( (((tlp(Tk,Lm,'DT',F1,F2), Ty, _) @ TT_VP, np:_~>s:dcl, _) @ TT_NP, s:dcl, _),  New_TT ) :-
	TLP = tlp(Tk,Lm,'DT',F1,F2),
	Ty = (np:_~>s:dcl) ~>np:_~>s:dcl,
	( TT_NP = ( (tlp(_,'the','DT',_,_), DT_Ty, _) @ TT_n, np:F3, _) %frac-93
	; TT_NP = ( TT_n, np:F3, _), DT_Ty = n:_~>np:F3, TT_n = (_, n:_, _) %%frac-99
	),
	New_TT_NP = ((TLP, DT_Ty, TLP_H) @ TT_n, np:F3, TLP_H),
	TLP_H = tlp(DT_Ty,Lm,'DT',F1,F2),   
	TT_VP = (_, np:_~>Val_Ty, VP_H),  
	( debMode('fix') -> report(['!!! Fix: attach remote DT to noun']); true ),
	New_TT =  (TT_VP @ New_TT_NP, Val_Ty, VP_H).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ((n->n @ everyone, n), np) ---> (every, n->np) @ (n->n @ person)
n_mod_everyone( (( TTn_mod @ (tlp(_,Lm,'DT',_,_),n:_,_), n:_, _), np:F1, _),  New_TTH ) :-
	nonvar(Lm),
	decompose_everyone(Lm, Quant, Noun),
	Quant_H = tlp(n:F2~>np:F1, Quant, 'DT', 'Ins', 'Ins'), 
	Quant_TTH = ( tlp(Quant, Quant, 'DT', 'Ins', 'Ins'), n:F2~>np:F1, Quant_H ),
	Noun_H = tlp(n:F2, Noun, 'NN', 'Ins', 'Ins'), 
	Noun_TTH = ( tlp(Noun, Noun, 'NN', 'Ins', 'Ins'), n:F2, Noun_H ),
	( debMode('fix') -> report(['!!! Fix: decompose GQ']); true ),
	New_TTH = (Quant_TTH @ (TTn_mod @ Noun_TTH, n:F2, Noun_H), np:F1, Quant_H). 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% someone,np -> some:n->np @ person:n 
some_one( (tlp(_,Lm,'DT',_Feat1,_),np:F1,_), New_TTH ) :-
	%nonvar(Lm),
	decompose_everyone(Lm, Quant, Noun),
	Quant_TTH = ( tlp(Quant, Quant, 'DT', 'Ins', 'Ins'), n:F2~>np:F1, Quant_H ),
	Quant_H = tlp(n:F2~>np:F1, Quant, 'DT', 'Ins', 'Ins'),
	Noun_TTH = ( tlp(Noun, Noun, 'NN', 'Ins', 'Ins'), n:F2, Noun_H ),
	Noun_H = tlp(n:F2, Noun, 'NN', 'Ins', 'Ins'),  
	( debMode('fix') -> report(['!!! Fix: decompose GQ']); true ),
	New_TTH = (Quant_TTH @ Noun_TTH, np:F1, Quant_H). 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% no,n~>np (sleeping:n~>n one:n) -> no,n~>np (sleeping:n~>n person:n)
some_sleeping_one( ( (tlp(Tk,'no',POS,Feat1,Feat2),n:F1~>np:F2,H) @ Noun_TT, np:F3, _Head), New_TTH ) :-
	nonvar(Tk),
	Noun_TT = ( Nmod @ (tlp(_,'one','NN',_,_),n:F,_), n:X, _),
	Person_TT = (tlp('person','person','NN','Ins','Ins'), n:F, Head_Per),
	Head_Per = tlp(n:F,'person','NN','Ins','Ins'), 
	( debMode('fix') -> report(['!!! Fix: GQ with verb']); true ),
	New_TTH = ( (tlp(Tk,'no',POS,Feat1,Feat2),n:F1~>np:F2,H) @ ( Nmod @ Person_TT, n:X, Head_Per), np:F3, H ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% [its, n,(np,s),s]  ---> [s, np,n,(np,s),s] @ [it, np] 
% sick-5003
poss_pr_to_s_pr( (tlp(_,Lm,'PRP$',_,_), Type, _), New_TTH ) :-
	Type = n:_~>np:_, % type before type raising
	nonvar(Lm),
	lemma_of_poss_pr(Lm, Lm_pr),
	H_pr = tlp(np:X, Lm_pr, 'PRP', 'Ins', 'Ins'), 
	TTH_pr = (tlp(Lm_pr, Lm_pr, 'PRP','Ins','Ins'), np:X, H_pr),
	Ty_s = np:X~>Type, % type before type raising
	H_s = tlp(Ty_s, '\'s', 'POS', 'Ins', 'Ins'),
	TTH_s = ( tlp('\'s', '\'s', 'POS', 'Ins', 'Ins'), Ty_s, H_s),  
	New_TTH = ( TTH_s @ TTH_pr, Type, H_s ).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% N of [the] dogs,np ---> N dogs
% fracas-46
numOfNNS_to_numNNS( (Num @ ((tlp(_,'of',_,_,_),_NP:_~>pp,_) @ NP, pp,_), np:_, _), New_TTH ) :-
	!,
	Num = (tlp(Tk,Lm,Pos,F1,F2), _, _),
	( Pos = 'CD' % fracas-46
	; member(Lm, ['none', 'all', 'each']) 
	),
	Head = tlp(n:_~>np:_,Lm,Pos,F1,F2),
	New_Num = (tlp(Tk,Lm,Pos,F1,F2),n:_~>np:_, Head), 
	once( ( NP = ((_Det,n:_~>np:_,_) @ N, np:_, _)
		  ; NP = (N, np:_ ,_), N = (_, n:_, _)  
		  ; NP = (_, n:_, _),  N = NP ) ), 
	( debMode('fix') -> report(['!!! Fix: 5 of Dogs -> 5 Dogs']); true ),
	New_TTH = (New_Num @ N, np:_, Head).

% None of [the] kids,n,np ---> None kids
%sick-122
numOfNNS_to_numNNS( ((((tlp(_,'of',_,_,_),_,_) @ NP, n:_~>n:_,_) @ Num, n:_,_), np:_,_),  New_TTH ) :-
	Num = (tlp(Tk,Lm,Pos,F1,F2), _, _),
	( Pos = 'CD' % fracas-46
	; member(Lm, ['none', 'all', 'each']) %sick-122
	),
	Head = tlp(n:_~>np:_,Lm,Pos,F1,F2),
	New_Num = (tlp(Tk,Lm,Pos,F1,F2),n:_~>np:_, Head), 
	once( ( NP = ((_Det,n:_~>np:_,_) @ N, np:_, _)
		  ; NP = (N, np:_ ,_), N = (_, n:_, _)  
		  ; NP = (_, n:_, _),  N = NP ) ), 
	( debMode('fix') -> report(['!!! Fix: 5 of Dogs -> 5 Dogs']); true ),
	New_TTH = (New_Num @ N, np:_, Head).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% All:PDT:np~>np the:n~>np dogs:n ---> All dogs 
%!!! should not be "not all", "not every"
% fracas-92
pdt_rm_dt_noun( (PDT @ ((tlp(_,_,'DT',_,_),n:_~>np:_,_) @ Noun, np:_,_), np:_, _), New_TTH ) :-
	PDT = (tlp(Tk,Lm,'PDT',F1,F2), np:_~>np:_, _),
	Head = tlp(n:_~>np:_,Lm,'DT',F1,F2),
	Det = (tlp(Tk,Lm,'DT',F1,F2),n:_~>np:_, Head), 
	( debMode('fix') -> report(['!!! Fix: attach pre determiner']); true ),
	New_TTH = (Det @ Noun, np:_, Head).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% not @ (all @ birds) -> not @ all @ birds
not_all_NN( (NOT @ ((ALL_TLP, n:_~>np:_, ALL_H) @ Noun, np:_, ALL_H), np:_, _), New_TTH ) :-
	NOT = (NOT_TLP, _, NOT_H), % pos = RB?
	ALL_TLP = tlp(_,_,'DT',_,_), %urgent, fracas-134, atomic list concat why removing this clause causes a problem?
	NOT_TLP = tlp(_,_,_,_,_),
	nonvar(NOT_H),	
	NOT_H =.. [tlp, _ | Rest], 
	Ty = (n:_~>np:_)~>n:_~>np:_,
	NOT_H1 =.. [tlp, Ty | Rest], 
	New_TTH = (((NOT_TLP, Ty, NOT_H1) @ (ALL_TLP, n:_~>np:_, ALL_H), n:_~>np:_, ALL_H) @ Noun, np:_, ALL_H), 
	( debMode('fix') -> report(['!!! Fix: not (all dogs) -> (not all) dogs']); true ).

% not @ everybody -> not @ every @ person
not_everybody( (NOT @ (EB_TLP, np:_, EB_H), np:_, EB_H), New_TTH ) :-
	nonvar(EB_TLP),
	EB = (EB_TLP, np:_, EB_H),
	EB_TLP = tlp(_,_,_,_,_),
	once(clean(EB, EB1)),
	EB1 = (_,np:_,EB1_H),
	( EB \= EB1 ->
		once(clean( (NOT@EB1, np:_, EB1_H), New_TTH)),
		( debMode('fix') -> report(['!!! Fix: not everybody -> (not every) person']); true )
	;	fail
	).
	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% make pp the most outter modifier of the head (pp is kinda intersective):  
% e.g. (A,n~>n) @ ((N,pp~>n) @ (P,pp)) --~> (P',n~>n) @ ((A,n~>n) @ (N',n)) 
/*n_pp_to_pp_n( (TT1 @ TT2, n:F2, H), (, n:F2, H) ) :-
	move_pp_up(TT1, TT2)

move_pp_up( (Fun, n:F11~>n:F12, H1) @ (Arg, _, H2),  (Fun, n:F11~>n:F12, H1) @ (Arg1, Ty, H2)    ) :-
	!,
	move_pp_up( Arg, (Arg1,Ty), TTpp)

move_pp_up( (Noun, pp~>n:F1, H1) @ (PP, pp, H2),  TTnoun, TTpp ) :-
	!,
	set_type_for_tt( (Noun,pp~>n:F1), n:F1, TTnoun ),
	set_type_for_tt( (PP,pp), n:X~>n:X, TTpp ).
*/

/*
nn_n( (X1@X2, n),  (tlp('NN@N','NN@N',_,_,_), n)) :-
	X1 = (tlp(_,_,_,_,_),n:_~>n:_),
	X2 = (tlp(_,_,_,_,_),n),
	term_to_atom(X1, At1),
	term_to_atom(X2, At2),
	write(At1), 
	write('\t\t'), 
	writeln(At2).
*/

	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
it_is_mod( A, B) :-
	A = ((_A1, T1~>T2) @ (A2, T1), T2),
	cat_eq(T1, T2),
	B = (A2, T2).	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
it_is_np( (X, np), (tlp(String,String,_,_,_),np) ) :-
	X \= tlp(_,_,_,_,_),
	tc_to_string((X,np), String).	
	%writeln(String)
	%latex_file_stream(S),
	%latex_ttTerm_print_tree(S, 6, (X, np))

% TC to String
tc_to_string(X,_) :- var(X), writeln('Variable accounted'), !, fail.

tc_to_string( (X,_), Str ) :-
	var(X), !,
	term_to_atom(X, StrX),
	atom_chars(StrX, [_, _ | Index_List]),
	X_Index_List = ['X' | Index_List], 
	atom_chars(Str, X_Index_List).
	
tc_to_string( (A @ B, _), Str ) :-
	tc_to_string(A, StrA),
	tc_to_string(B, StrB),
	atomic_list_concat([StrA, ' ', StrB], Str).

tc_to_string( (tlp(A,_,_,_,_),_), A ).

tc_to_string( (A,_), Str ) :-
	tc_to_string(A, Str).

tc_to_string( (abst(A, B),_), Str ) :-
	tc_to_string(A, StrA),
	tc_to_string(B, StrB),
	atomic_list_concat(['(', StrA, '.', StrB, ')'], Str).





	
