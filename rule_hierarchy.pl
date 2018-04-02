%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Rule dependencies
% temporarily sub_rule is not transitive

sub_rule(A, B) :- % non reflexive
	prop_sub_rule(A, C),
	sub_rule_(C, [C], B).

sub_rule_(X, _, X).  


sub_rule_(A, Path, B) :-
	prop_sub_rule(A, C),
	\+member(C, Path),
	sub_rule_(C, [C|Path], B).

prop_sub_rule( 	h(up_mon_fun_some,	[],	[X,Y],	[A,B,_]), 
				h(up_mon_fun, 	   	[],	[X,Y], 	[A,B]) 
).
 
prop_sub_rule( 	h(up_mon_fun_some, 	[],	[X,_],	[A,_,C]), 
			    h(tr_a, 		   	[],	[X],	[C,A])
).

prop_sub_rule( 	h(up_mon_fun_some, 	[],	[_,F],	[_,B,C]), %!!!exp
			    h(fl_a_c, 		   	[],	[F,C],	[B])
).

%prop_sub_rule(	h(up_mon_fun_some, 	[X,_],	[A,_,C]), 
%			   	h(the_c, 			[X,_C],	[A])
%). % since up_mon_fun_some does not contain 'the'

% prop_sub_rule( [up_mon_fun_some, X, Y, AppInfo], [fl_a, Y, AppInf]).

prop_sub_rule( 	h(dw_mon_args,	[],	[X,Y],	[A,B]),
				h(dw_mon, 		[],	[X,Y],	[_,_,A,B])  %!!! before were x, 
).

prop_sub_rule(  h(up_mon_args, 	[],	[X,Y],	[A,B]), 
				h(up_mon, 		[],	[X,Y],	[_,_,A,B]) 
).

prop_sub_rule( 	h(dw_mon_fun, 	[],	[X,Y],	[A,B]), 	
				h(dw_mon, 		[],	[X,Y],	[A,B,_,_]) 
).

prop_sub_rule( 	h(up_mon_fun, 	[],	[X,Y], 	[A,B]),
				h(up_mon, 		[],	[X,Y],	[A,B,_,_])
).

prop_sub_rule( 	h(int_mod_tr, 	[],	[X],	[A,_]),
				h(push_mod, 		[],	[X],	[A]) 
).

prop_sub_rule( 	h(int_mod_tr, 	[],	[X], 	[A,_]),
				h(mod_n_tr, 	[],	[X],	[A])
).
/*
prop_sub_rule( 	h(tr_conj_and, 	[X],	[_,B]), 	
				h(mod_tr, 		[X],	[B]) 
).

prop_sub_rule( 	h(tr_conj_who, 	[X], 	[_,B]),
				h(mod_tr, 		[X],	[B])	 
).

prop_sub_rule( 	h(tr_disj_or, 	[X], 	[_,B]),
				h(mod_tr, 		[X],	[B]) 
).

prop_sub_rule( 	h(tr_if, 		[X],	[_,B]),
				h(mod_tr, 		[X],	[B]) 
).
*/

%prop_sub_rule( 	h(fun_dist_np,		[],	[X],	[A]),
%				h(fun_dist, 		[],	[X],	[A])
%).

prop_sub_rule( 	h(mod_vac, 			[],	[X],	[A]),
				h(push_mod, 		[],	[X],	[A])
).

prop_sub_rule( 	h(push_mod, 		[],	[X], 	[A]),
				h(mod_vac, 			[],	[X],	[A])
).

prop_sub_rule( 	h(mod_n_tr, 		[],	[X], 	[A]),
				h(push_mod, 		[],	[X],	[A])
).

prop_sub_rule( 	h(the_c, 		[],	[X,N], 	[V]),
				h(the, 			[],	[X],	[V,N|_]) 
). 

prop_sub_rule( 	h(the, 			[],	[X], 	[V,N|_]), % may introduce more than 2 nodes
				h(the_c, 		[],	[X,N],	[V]) 
). 

%prop_sub_rule( [the, X], 		[the_c, X, _]).  % removing this allows to assert VP on new constant of type N

%prop_sub_rule( [the_c, X, _], 	[tr_a, X] ). 
%prop_sub_rule( [tr_a, X],       [the_c, X, _] ).

prop_sub_rule( 	h(tr_every_c, 	[C],	[X,_],	[_]),
				h(tr_every, 	[C],	[X],	[_,_,_])   %why tr_every cannot apply to diff constant?
). 

prop_sub_rule(	h(fl_a_c,	[C],	[X,_],	[_]),  	
				h(fl_a, 	[C],	[X], 	[_,_,_])
). 

prop_sub_rule(	h(tr_no_c,	[C],	[X,_],	[_]),  	
				h(tr_no, 	[C],	[X], 	[_,_,_])
). 

%fl_a -> the is not necessary since the-rule won't be applicapble, branch will close before that


