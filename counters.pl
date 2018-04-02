%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Description: Tableau Prover for Natural Logic
%     Version: 12.06.12
%      Author: lasha.abzianidze{at}gmail.com 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% 			Counters for IDs, 
%	  fresh constants ((non-)entities) 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% entity_index(N)
% counter of the index for fresh entity constants
:- dynamic entity_index/1.
entity_index(0).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% new_entity_index(N) :-
% creates the next new index N for fresh entity constant
new_entity_index(M) :-
	entity_index(N),
	retract(entity_index(N)),
	M is N+1,
	%(0 is M mod 10 -> display(M), nl; true), 
	asserta(entity_index(M)).
	
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% const_index(N)
% counter of the index for fresh non-entity constants
:- dynamic const_index/1.
const_index(0).	


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% new_const_index(N) :-
% creates the next new index N for fresh non-entity constant
new_const_index(M) :-
	const_index(N),
	retract(const_index(N)),
	M is N+1,
	%(0 is M mod 10 -> display(M), nl; true), 
	asserta(const_index(M)).	
	
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% reset_const_index
% resets the index for both entity and non-entity constants to 0
reset_const_index :-
	retract(const_index(_)),
	asserta(const_index(0)),
	retract(entity_index(_)),
	asserta(entity_index(0)).	

	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% id_count(N)
% counter of IDs for the nodes of a tableau tree
% counter is set to 2 since a premise and a conclusion
% are initial nodes of a tableau tree   
:- dynamic id_count/1.
id_count(2).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% new_id_count(N)
% creates the next new ID N for a new node
new_id_count(M) :-
	id_count(N) ->
		retract(id_count(N)),
		(var(M) -> 
			M is N+1;
			true),
		asserta(id_count(M));
	M = 1,
	asserta(id_count(M)).
	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% reset_id_count
% resets ID to 2
reset_id_count :-
	retract(id_count(_)),
	assertz(id_count(2)),
	!.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% event_index(N)
% counter of the index for events
:- dynamic event_index/1.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% new_entity_index(N) :-
% creates the next new index N for fresh entity constant
new_event_index(M) :-
	event_index(N) ->
		retract(event_index(N)),
		M is N+1,
		%(0 is M mod 10 -> display(M), nl; true), 
		asserta(event_index(M));
	asserta(event_index(0)),
	M = 0.


