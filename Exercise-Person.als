abstract sig Person{
	children: set Person,		// field Person: children is a subset of P x P
	siblings: set Person,		// two subset Person
	parents: some Person
}

sig Man, Woman extends Person {} 	// two subsets of Person

sig Married in Person{		// in: define a set of properties of a sig
	spouse: one Married		// just one Married status of a person
}

fact oneFatherAndMother{
	all p: Person |		//for all people
		(lone (p.parents & Man)) 	//father
			and (lone (p.parents & Woman))	//mother
}

/*
A person P’s siblings are those people with the same parents as P (excluding P) 
*/
fact theSibling{
	all p: Person |
		p.siblings = {q: Person | p.parents = q.parents} - p
}

pred show{}

run show
