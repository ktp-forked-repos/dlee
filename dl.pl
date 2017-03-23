
[library(clpq)].
[library(assoc)].
[library(pairs)].


/* non-dict concepts */
c(concept).  /* the most general concept is called concept */
c(voltage).
c(resistance).
c(current).

/* dict-based concepts */
c(conductor{voltage:U,current:I,resistance:R,power:P}).
c(ohmic_conductor{}).
c(two_terminals{a:A, b:B}).
c(lamp{}).
c(wire{}).
c(resistor{}).
c(battery{minus:A,plus:B,voltage:U,power:P,current:I}).
c(r100{resistance:100}).
c(law{}).
c(ohm_law{voltage:U,resistance:R,current:I}) :- { U = R * I }.
c(power_law{power:P,voltage:U,current:I}) :- { P = U * I }.
c(kirchoff{}).
c(kirchoff_current{current:I}).
c(kirchoff_voltage{voltage:U}).


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
	print(T),

	dict_create(C,T,DictData),
	print("done"),
	C0 :< C.

concept(union(A,B)) :- concept(A), concept(B).

concept(intersection(A,B)) :- concept(A), concept(B).

create_dict_data([],[]).
create_dict_data([H|T],R) :-
	atom(H), !, find_c_by_atom(H,H1),
	dict_pairs(H1,Tag,Pairs),
	create_dict_data(T,R0),
	union(Pairs,R0,R).


/* ------------- ontology rules ---------------*/
/* is a */
r(ohmic_conductor, is_a, conductor).
r(lamp, is_a, two_terminals).
r(lamp, is_a, ohmic_conductor).
r(wire, is_a, two_terminals).
r(wire, is_a, ohmic_conductor).
r(resistor, is_a, two_terminals).
r(resistor, is_a, ohmic_conductor).
r(r100, is_a, resistor).
r(w, is_a, wire).
r(power_law, is_a, law).
r(ohm_law, is_a, law).
r(kirchoff, is_a, law).
r(kirchoff_current, is_a, kirchoff).
r(kirchoff_voltage, is_a, kirchoff).

/* applies to */
r(ohm_law, applies_to, ohmic_conductor).
r(power_law, applies_to, conductor).
r(kirchoff, applies_to, branch).

r(Dict,is_a,Tag) :-
	ground(Dict),
	c(Dict),
	is_dict(Dict,Tag).
r(Dict,is_a,Tag) :-
	ground(Tag),
	not(is_dict(Tag)),
	concept(Dict),
	is_dict(Dict,Tag).

/* concept inheritance processing rules */
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

role(X,applies_to,Y) :- true. /* TODO */


/* THE PERCEIVED REALITY IN THE BEGINNING */
abox( [ lamp{ resistance:3, voltage:12 } ] ).


/* API for the app */
run(Result) :-
	abox( Facts ), /* set of facts [Fact1, Fact2, Fact3 | RestFacts ] */
	apply_semantics(Facts,Result).

apply_semantics([],[]).

apply_semantics([F|R],[C|RestRes]) :-
	concept(C1),
	is_dict(C1,Tag),
	F :< C1,
	role(Tag,is_a,Concept) ; /* otherwise: */ Concept = Tag,
	role(X,applies_to,Concept,C0),   /* TODO: for all X */
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













