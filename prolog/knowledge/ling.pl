%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% 	predicates for Linguistic processing
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- module(ling, [
	a_list_of_colors/1,
	decompose_everyone/3,
	lemma_of_poss_pr/2,
	pos2s_feat/2,
	text_to_number/2
]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% lemma of a possessive pronoun
lemma_of_poss_pr('my', 	 'I').
lemma_of_poss_pr('your', 'you').
lemma_of_poss_pr('its',  'it').
lemma_of_poss_pr('our',  'we').
lemma_of_poss_pr('their','they').


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% detect a quantifier and a head noun from a word
% everyone -> every person
decompose_everyone(Word, Quant, Head) :-
	member(Word, ['everybody', 'everyone']) -> (Quant, Head) = ('every', 'person');
	member(Word, ['somebody', 'someone']) -> (Quant, Head) = ('a', 'person');
	member(Word, ['nobody']) -> (Quant, Head) = ('no', 'person');
	Word = 'everything' -> (Quant, Head) = ('every', 'thing');
	Word = 'something' -> (Quant, Head) = ('some', 'thing');
	Word = 'nothing' -> (Quant, Head) = ('no', 'thing');
	% NL
	% note that een/geen wouldn't be replced with a/no at this stage, so using a/no
	Word = 'iemand' -> (Quant, Head) = ('a', 'persoon');
	Word = 'niemand' -> (Quant, Head) = ('no', 'persoon');
	Word = 'iets' -> (Quant, Head) = ('a', 'entiteit');
	Word = 'niets' -> (Quant, Head) = ('no', 'entiteit');
	Word = 'iedereen' -> (Quant, Head) = ('every', 'persoon').


%text_to_number(Atom, Num) :-

text_to_number('a', 	1).
text_to_number('one', 	1).
text_to_number('two', 	2).
text_to_number('three', 3).
text_to_number('four', 	4).
text_to_number('five', 	5).
text_to_number('six', 	6).
text_to_number('seven', 7).
text_to_number('eight', 8).
text_to_number('nine', 	9).
text_to_number('ten', 	10).


a_list_of_colors([
'brown', 'blue', 'black', 'blond', 'beige',
'cyan',
'gray', 'green',
'magenta',
'orange',
'pink', 'purple',
'red',
'violet',
'white',
'yellow'
]).


pos2s_feat(POS, Feat) :-
	memberchk(POS, ['VBD','VBP','VBZ']) -> Feat = 'dcl'
	; memberchk(POS, ['VB']) -> Feat = 'b'
	; memberchk(POS, ['VBG']) -> Feat = 'ng'
	; memberchk(POS, ['VBN']) -> Feat = 'pss'
	; atom_prefix(POS, 'JJ') -> Feat = 'adj'
	; fail. % what about s:pt?
