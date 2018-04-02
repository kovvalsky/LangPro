
correct_ccgTerm(Term, SimCorrTerm) :-
	add_heads(Term, Term_H), % binds category features
	ccgTerm_to_llf(Term_H, CorrTerm_H),
	add_heads(CorrTerm, CorrTerm_H),
	simplify(CorrTerm, SimCorrTerm).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
add_heads( (Tr,Ty), (Tr,Ty,_H) ) :-
	var(Tr), !.
	
add_heads( (Tr,Ty), (Term_H,Ty,_H) ) :- %heads can change in lx rules
	Tr = (Tr1,Ty1),
	Term_H = (_,Ty1,_), !,
	add_heads((Tr1,Ty1), Term_H).
	 
add_heads( (Abst,Type), (Abst_H,Type,H) ) :-
	Abst = abst(TTX, (Tr,Ty)), 
	Abst_H = abst( (TTX,_), (Tr_H,Ty,H) ), !,
	add_heads((Tr,Ty), (Tr_H,Ty,H)). %some details needed
	
	
add_heads( (App,Type), (App_H,Type,H) ) :-
	App = (Tr1, Ty1) @ (Tr2, Ty2), 
	App_H = (Tr1_H1,Ty1,H1)@(Tr2_H2,Ty2,H2), !,
	add_heads((Tr1, Ty1), (Tr1_H1, Ty1, H1)),
	add_heads((Tr2, Ty2), (Tr2_H2, Ty2, H2)), %some details needed
	detect_head((Ty1,H1), (Ty2,H2), H).   

add_heads((TLP,Ty), (TLP,Ty,H)) :-
	TLP = tlp(_,Lm,Pos,F1,F2),
	H = tlp(Ty,Lm,Pos,F1,F2).
	 	


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%detect_head( (Ty~>Ty, _), (Ty, H2), H2 ) :- !.

detect_head( (Ty2~>Ty1, _), (Ty2, H2), H2 ) :-
	cat_eq(Ty1, Ty2), !.  % binds category features
	 	
detect_head( (_, H1), (_, _), H1 ) :-
	!.

detect_head( (_, _), (_, _), _). % for removing heads since word substitutions cannot project upwards 



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% replace some -> a, every -> all
% plural to singular

simplify((Var, Type), (Var, Type)) :-
	var(Var), !.

simplify((TT1 @ TT2, Type), (SimTT1 @ SimTT2, Type)) :-
	!, simplify(TT1, SimTT1),
	simplify(TT2, SimTT2).

simplify( (abst(TTx, TT), Type), (abst(TTx, SimTT), Type) ) :-
	!, simplify(TT, SimTT).	

% treats all constant:np as constant:e
%simplify( (tlp(Tk,Lem,Pos,F1,F2), np:X),  SimTT) :-
%	X \= 'thr',
%	simplify( (tlp(Tk,Lem,Pos,F1,F2), e), SimTT), %e.g. people -> person
%	!.

simplify( (tlp(_Tk,Lem,'NNS',F1,F2), Type),  SimTT) :-
%simplify( (tlp(_Tk,Lem,'NNS',F1,F2), Type),  (tlp(Lem,Lem,'NN',F1,F2), Type) ) :-
	simplify( (tlp(Lem,Lem,'NN',F1,F2), Type), SimTT), %e.g. people -> person
	!.

% substitute possesive pronouns with 'the' sick-240
simplify( (tlp(_Tk,_Lem,'PRP$',F1,F2), Type),  SimTT) :-
	SimTT = (tlp('the','the','DT',F1,F2), Type), 
	!.

% atomic PPs to atomic PR (simplier solution than changing rules and extractor)
simplify( (tlp(Tk,Lm,IN_WDT,F1,F2), pp),  SimTT) :-
	SimTT = (tlp(Tk,Lm,IN_WDT,F1,F2), pr), 
	!.

% substitute relative that by who %test
simplify( (tlp('that','that',IN_WDT,F1,F2), (np:A~>s:B)~>n:C~>n:D),  SimTT) :- % what?
	SimTT = (tlp('who','who',IN_WDT,F1,F2), (np:A~>s:B)~>n:C~>n:D), 
	!.

simplify( (tlp(Tk,Lem,Pos,F1,F2), Type), (tlp(Tk,Lemma,Pos,F1,F2), Type) ) :-
	!, 
	( Lem = 'none', Lemma = 'no';
	  Lem = 'which', Lemma = 'who'; % what about tokens? why dont u change them?
	  Lem = 'some',Lemma = 'a';
	  Lem = 'an',  Lemma = 'a';	
	  Lem = 'all', Lemma = 'every'; % all cake =\= each cake
	  Lem = 'each', Lemma = 'every';
	  Lem = 'a_lot_of', Lemma = 'many';	
	  Lem = 'neither', Lemma = 'no'; % fracas-46, but neither has a presupposition
	  Lem = 'people', Lemma = 'person';		
	  %Lem = 'the', Lemma = 'a'; %what about the dogs? % the concert means only one concert in the branch
	  %Lem = 's', Lemma = 'a';	% ignore plurals	
	  Lemma = Lem ), !.

simplify( (TT, Type), (SimTT, Type) ) :-
	!, simplify(TT, SimTT). 



	




