%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Description: Lexicon
%     Version: 12.06.12
%      Author: lasha.abzianidze{at}gmail.com 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%           Lexicon of constants
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%:- dynamic lex/2.

%'John' :: e :: nil.
%'Mary' :: e :: nil.
%'Emily' :: e :: nil.

'John' :: np:_ :: nil.
'Sam' :: np:_ :: nil.
'Mary' :: np:_ :: nil.
'Emily' :: np:_ :: nil.
'Ann' :: np:_ :: nil.
'Kate' :: np:_ :: nil.


% Lexicon for ttExp_to_ttTerm
%some :: n:_ ~> np:_ :: [up,up].
%a :: n:_ ~> np:_ :: [up,up].
some :: n:_ ~> (np:_~>s:_) ~> s:_ :: [up,up].
%every :: n:_ ~> np:_ :: [up,up].*/


% non monotone a
a :: n:_ ~> (np:_~>s:_) ~> s:_ :: [non,non]. % no monotonicity
a :: (e ~> t) ~> (e ~> t) ~> t :: [non,non]. % a=some=an=the
the :: n:_ ~> (np:_~>s:_) ~> s:_ :: [non,non]. % can be "up", because up_mon_fun can apply earlier than tr_a (see frac-249) 

% monotone a
%a :: n:_ ~> (np:_~>s:_) ~> s:_ :: [up,up]. % no monotonicity
%a :: (e ~> t) ~> (e ~> t) ~> t :: [up,up]. % a=some=an=the
%the :: n:_ ~> (np:_~>s:_) ~> s:_ :: [up,up]. 


both :: n:_ ~> (np:_~>s:_) ~> s:_ :: [non,up]. 
neither :: n:_ ~> (np:_~>s:_) ~> s:_ :: [non,dw]. % fracas-30
%an :: (e ~> t) ~> (e ~> t) ~> t :: [up,up]. %!!!
%the :: (e ~> t) ~> e :: [non]. %!!!

than :: np:_ ~> (np:_~>s:_) ~> np:_~>s:_ :: [non,up,non]. %!!! exp
than :: np:_ ~> (np:_~>s:_) ~> np:_~>s:_ :: [non,dw,non]. %!!! exp

s :: n:_ ~> (np:_~>s:_) ~> s:_ :: [up,up].
s :: (e ~> t) ~> (e ~> t) ~> t :: [up,up]. %!!! non linguistic one, plural
several :: n:_ ~> (np:_~>s:_) ~> s:_ :: [up,up].
several :: (e ~> t) ~> (e ~> t) ~> t :: [up,up]. %!!! non linguistic one, plural
every :: (e ~> t) ~> (e ~> t) ~> t :: [dw,up]. % every=each
every :: n:_ ~> (np:_~>s:_) ~> s:_ :: [dw,up].
%each :: (e ~> t) ~> (e ~> t) ~> t :: [dw,up].
most :: (e ~> t) ~> (e ~> t) ~> t :: [non,up].
most :: n:_ ~> (np:_~>s:_) ~> s:_ :: [non,up].
%who :: (e ~> t) ~> (e ~> t) ~> e ~> t :: [non,non,non]. %!!!
%whom :: (e ~> t) ~> (e ~> t) ~> e ~> t :: [non,non,non]. %!!!
no :: n:_ ~> (np:_~>s:_) ~> s:_ :: [dw,dw].
no :: (e ~> t) ~> (e ~> t) ~> t :: [dw,dw].
few :: n:_ ~> (np:_~>s:_) ~> s:_ :: [dw,dw].
few :: (e ~> t) ~> (e ~> t) ~> t :: [dw,dw].

many :: n:_ ~> (np:_~>s:_) ~> s:_ :: [non,up].

'\'s' :: np:_ ~> n:_ ~> (np:_ ~> s:_) ~> s:_ :: [non,up,up]. 


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Adjectives, adverbs
difficult :: _ ~> np:_ ~> s:_ :: [dw, non].



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
woman 	:: e ~> t :: [non].
man 	:: e ~> t :: [non].
person 	:: e ~> t :: [non].
student :: e ~> t :: [non].
bird 	:: e ~> t :: [non].
dog 	:: e ~> t :: [non].
girl 	:: e ~> t :: [non].
boy 	:: e ~> t :: [non].
cat 	:: e ~> t :: [non].
hound 	:: e ~> t :: [non].
animal 	:: e ~> t :: [non].
lark 	:: e ~> t :: [non].
human 	:: e ~> t :: [non].
bachelor ::e ~> t :: [non].

woman 	:: n:_ :: nil.
man 	:: n:_ :: nil.
person 	:: n:_ :: nil.
student :: n:_ :: nil.
bird 	:: n:_ :: nil.
dog 	:: n:_ :: nil.
girl 	:: n:_ :: nil.
boy 	:: n:_ :: nil.
cat 	:: n:_ :: nil.
hound 	:: n:_ :: nil.
animal 	:: n:_ :: nil.
lark 	:: n:_ :: nil.
human 	:: n:_ :: nil.
bachelor ::n:_ :: nil.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
walk 	:: np:_ ~> s:_ :: [non].
sleep 	:: np:_ ~> s:_ :: [non].
snore 	:: np:_ ~> s:_ :: [non].
talk 	:: np:_ ~> s:_ :: [non].
love 	:: np:_ ~> np:_ ~> s:_ :: [non,non].
like 	:: np:_ ~> np:_ ~> s:_ :: [non,non].
touch 	:: np:_ ~> np:_ ~> s:_ :: [non,non].
kiss 	:: np:_ ~> np:_ ~> s:_ :: [non,non].
move 	:: np:_ ~> s:_ :: [non].
run 	:: np:_ ~> s:_ :: [non].
fly 	:: np:_ ~> s:_ :: [non].
be 		:: np:_ ~> np:_ ~> s:_ :: [non,non].

is ::  e ~> e ~> t :: [non, non]. %!!!

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
if :: s:_ ~> s:_ ~> s:_ :: [non, non].
who :: (np:_~>s:_) ~> n:_ ~> n:_ :: [non, non].
and :: Type ~> Type ~> Type :: [non, non].
but :: Type ~> Type ~> Type :: [non, non]. % careful
when :: Type ~> Type ~> Type :: [non, non].
although :: Type ~> Type ~> Type :: [non, non].
or :: Type ~> Type ~> Type :: [non, non].
not :: Type ~> Type :: [non].
%if :: t ~> t ~> t :: [dw, up].
%and :: Type ~> Type ~> Type :: [up,up].
%or :: Type ~> Type ~> Type :: [up,up].
%not :: Type ~> Type :: [dw].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
to 		:: e ~> e ~> t :: [up, up]. %!!!
in 		:: e ~> e ~> t :: [up, up]. %!!!
into	:: e ~> e ~> t :: [up, up]. %!!!
on 		:: e ~> e ~> t :: [up, up]. %!!!
of 		:: e ~> e ~> t :: [up, up]. %!!! mother of John is entity not predicate
for 	:: e ~> e ~> t :: [up, up]. %!!!
by 		:: e ~> e ~> t :: [up, up]. %!!!
over	:: e ~> e ~> t :: [up, up]. %!!!
at 		:: e ~> e ~> t :: [up, up]. %!!!
with 	:: e ~> e ~> t :: [up, up]. %!!!
without	:: e ~> e ~> t :: [up, up]. %!!!
after 	:: e ~> e ~> t :: [up, up]. %!!!
before 	:: e ~> e ~> t :: [up, up]. %!!!
from 	:: e ~> e ~> t :: [up, up]. %!!!
via     :: e ~> e ~> t :: [up, up]. %!!!
inside  :: e ~> e ~> t :: [up, up]. %!!!
among	:: e ~> e ~> t :: [up, up]. %!!!
amid	:: e ~> e ~> t :: [up, up]. %!!!

during 	:: e ~> e ~> t :: [up, up]. %!!!
while 	:: e ~> e ~> t :: [up, up]. %!!!
until 	:: e ~> e ~> t :: [up, up]. %!!!
despite	:: e ~> e ~> t :: [up, up]. %!!!
against :: e ~> e ~> t :: [up, up]. %!!!
about	:: e ~> e ~> t :: [up, up]. %!!!
since	:: e ~> e ~> t :: [up, up]. %!!!

because	:: e ~> e ~> t :: [up, up]. %!!!
so 	:: e ~> e ~> t :: [up, up]. %!!!

en	 	:: e ~> e ~> t :: [up, up]. %!!!
per 	:: e ~> e ~> t :: [up, up]. %!!!
as 		:: e ~> e ~> t :: [up, up]. %!!!
like 	:: e ~> e ~> t :: [up, up]. %!!!

accord 	:: e ~> e ~> t :: [up, up]. %!!!
regardless 	:: e ~> e ~> t :: [up, up]. %!!!

along 	:: e ~> e ~> t :: [up, up]. %!!!
above	:: e ~> e ~> t :: [up, up]. %!!!
under	:: e ~> e ~> t :: [up, up]. %!!!
near 	:: e ~> e ~> t :: [up, up]. %!!!
within  :: e ~> e ~> t :: [up, up]. %!!!
between :: e ~> e ~> t :: [up, up]. %!!!
behind  :: e ~> e ~> t :: [up, up]. %!!!
down    :: e ~> e ~> t :: [up, up]. %!!!
ago     :: e ~> e ~> t :: [up, up]. %!!!
prior   :: e ~> e ~> t :: [up, up]. %!!!

%sem(a, abst(P, abst(Q, a @ P @ @)), 

'Univ' :: e ~> t :: [non].
'*' :: _ :: [non].
event_time :: _ ~> e~> t :: [non, non]. %!!!  
rel :: _ ~> e ~> t :: [non, non]. %!!!
part_of :: e~>e~>t :: [non, non]. %!!!


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% adjectives
intersective_adjectives(
['italian', 'red', 'black', 'four-legged', 'alone', 'lone', 'topless']
).

privative_adjectives(
['former']
).

intersective(Lem) :-
	( (intersective_adjectives(List), member(Lem, List))
	; (a_list_of_colors(Colors), member(Lem, Colors)) 
	), !.

privative(Adj) :-
	privative_adjectives(List),
	member(Adj, List), !.


factive_verbs(
['see', 'know', 'regret']
).

factive(Verb) :-
	factive_verbs(List),
	member(Verb, List), !.

	
	
 



	


