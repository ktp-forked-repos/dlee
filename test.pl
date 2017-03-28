
[library(clpq)].
[library(assoc)].
[library(pairs)].


/* non-dict concepts */
d(concept).  /* the most general concept is called concept */
d(voltage).
d(resistance).
d(current).
d(plus).
d(minus).
d(power).

/* dict-based concepts */
d(conductor,conductor{voltage:U,current:I,resistance:R,power:P}).
d(ohmic_conductor,ohmic_conductor{},[conductor]).
d(two_terminals,two_terminals{a:A, b:B}).
d(battery,battery{minus:A,plus:B,voltage:U,power:P,current:I}).
d(law,law{}).
d(lamp,lamp{},[ohmic_conductor,two_terminals]).
d(wire,wire{},[conductor]).
d(resistor,resistor{},[ohmic_conductor]).
d(r100,r100{resistance:100},[resistor]).
d(ohm_law,ohm_law{voltage:U,resistance:R,current:I},[law]) :- { U = R * I }.
d(power_law,power_law{power:P,voltage:U,current:I}) :- { P = U * I }.

% Kirchoff laws
d(kirchoff,kirchoff{}).
d(kirchoff_current,kirchoff_current{current:I,a:A,b:B},[kirchoff]) :-
	sum_current(A, ASum), sum_current(B, BSum), ASum = BSum.
d(kirchoff_voltage,kirchoff_voltage{voltage:U,a:A,b:B},[kirchoff]) :-
	sum_voltage(A, ASum), sum_voltage(B, BSum), ASum = BSum.

% Circuit consist of elements and branches
d(circuit,circuit{elements:E,branches:B}).
d(branch,branch{a:Minus,b:Plus,current:I,voltage:U},[kirchoff]).

% Formulas for Kirchoff laws calculations
sum_current([],0).
sum_current([_{current:I}|T],Total) :- sum_current(T,Subsum),Total=I+Subsum.
sum_voltage([],0).
sum_voltage([_{voltage:U}|T],Total) :- sum_voltage(T,Subsum),Total=U+Subsum.


abox([C]) :-
	Acc=battery{minus:B1,plus:B2,voltage:12},
	B1=branch{a:[[Acc,minus]],b:[[Lamp,a]]},
	Lamp=lamp{a:B1,b:B2,power:60},
	B2=branch{a:[[Lamp,b]],b:[[Acc,plus]]},
	C=circuit{elements:[Acc,B1,Lamp,B2],branches:[B1,B2]}.


% Query concept by
% a) atom name
% b) (partly instantiated) subdict
% c) (partly instantiated) dict

concept(C,Def) :- d(C), atom(C).
concept(C,Def) :- d(C, Def), atom(C).
concept(C,Def) :- is_dict(C,Tag),d(Tag,Def),C:<Def.

/*
concept(C,Def) :-
	d(C0, Def0, SuperCs),
	concept0(SuperCs, SS),

	concept(C :< C1,

super_concepts(C, [concept]) :-
	atom(C),
	(not(d(C,_,_)) ; d(C,_,[concept]).
super_concepts(C, Result) :-
	atom(C),
	d(C,_,S),
*/

find_c_by_atom(C,Dict) :-
	c(Dict),
	is_dict(Dict),
	dict_pairs(Dict,C,_).

/* non-dict concepts */
concept(C) :- c(C), not(is_dict(C)).

/* handle concepts having no superconcept */
concept(C) :-
	c(C),
	is_dict(C,T),
	not(role(T,is_a_direct,_)).

/* handle concepts having superconcept(s) */
/* this time we should make a union of all dict properties */
concept(C) :-
	c(C0), /* it has to be concept */
	is_dict(C0,T),/* it has to be dict */
	findall(S,role(T,is_a,S),SCs), /* find all superconcepts SCs */
	/* make a union of all props in superconcepts */
	create_dict_data([T|SCs],DictData),
	dict_create(C,T,DictData),
	C0 :< C.
/*
concept(union(A,B)) :- concept(A), concept(B).

concept(intersection(A,B)) :- concept(A), concept(B).
*/
create_dict_data([],[]).
create_dict_data([H|T],R) :-
	atom(H), !, find_c_by_atom(H,H1),
	dict_pairs(H1,Tag,Pairs),
	create_dict_data(T,R0),
	union(Pairs,R0,R).


/* ------------- ontology rules ---------------*/
/* applies to */
r(ohm_law, applies_to, ohmic_conductor).
r(power_law, applies_to, conductor).
r(kirchoff, applies_to, branch).

/*
 *
 * */
r(Dict,is_a,Tag) :-
	ground(Dict),
	c(Dict),
	is_dict(Dict,Tag).
r(Dict,is_a,Tag) :-
	ground(Tag),
	not(is_dict(Tag)),
	concept(Dict),
	is_dict(Dict,Tag).

/* every role, which is true for a concept, is also true for all subconcepts concept inheritance processing rules */

r(MoreConcrete, R, Whatever) :-
	ground(R), R \= is_a,
	role(MoreConcrete, is_a, Abstract),
	r(Abstract, R, Whatever).

r(Whatever, R, MoreConcrete) :-
	ground(R), R \= is_a,
	role(MoreConcrete, is_a, Abstract),
	r(Whatever, R, Abstract).

/* OHM law */
/*
role(	ohm_law{voltage:U,current:I,resistance:R},
	applies_to,
	ohmic_conductor, _{voltage:U,current:I,resistance:R}) :-
	{ U = R * I }.*/

/* POWER law */
/*
role(   power_law{power:P,voltage:U,current:I},
	applies_to,
	conductor, _{power:P,voltage:U,current:I}) :-
	{ P = U * I }.*/


/* is_a is associative. Therefore role(X,is_a,Y) produces any combinations
of the is_a relation (closure in terms of is_a) */
role(X,is_a,Y) :- r(X,is_a,Y).
role(X,is_a,Y) :- r(X,is_a,Z), role(Z,is_a,Y).

/* role(X,is_a_direct,Y) produces only a set of direct is_a relations */
/* all the concepts are direct subconcept of 'concept' */
role(X,is_a_direct,Y) :- r(X,is_a,Y).

role(A,applies_to,B) :-
	r(X,applies_to,Y),
	concept(B), is_dict(B,Y),
	concept(A), is_dict(A,X),
	dict_pairs(A,_,Pairs),
	dict_create(Result,_,Pairs),
	Result :< B.


/* THE PERCEIVED REALITY IN THE BEGINNING */
abox( [ lamp{ resistance:3, voltage:12 } ] ).


/* API for the app */
run(Result) :-
	abox( Facts ), /* set of facts [Fact1, Fact2, Fact3 | RestFacts ] */
	apply_semantics(Facts,Result).

apply_semantics([],[]).

apply_semantics([F|R],[C|RestRes]) :-
	atom(F),
	apply_semantics(R,[C|RestRes]).

apply_semantics([RawConcept|R],[C|RestRes]) :-
	concept(Concept),
	is_dict(Concept,Tag),
	RawConcept :< Concept,
	role(Tag,is_a,Concept) ; /* otherwise: */ Concept = Tag,
	role(X,applies_to,Concept),   /* TODO: for all X */
	C0 :< C,
	apply_semantics(R,RestRes).

/* TODO, ei toimi
analyzes([F|R],[C|RestRes]) :-
	concept(C0),
	is_dict(C0,Tag),
	F :< C0,
	findall(X,
	        ( ( role(Tag,is_a,Super), ! ; Super = Tag ),
		role(X,applies_to,Super,C1),   /* TODO: for all X */
	        C1 :< X),
		Z),
	matchall(Z,C),
	analyzes(R,RestRes). */
matchall([H],H).
matchall([H|T],H) :- matchall(T,H).













