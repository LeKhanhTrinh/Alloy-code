module simple_example

//A person has at most one father and mother
abstract sig Person {
  father: lone Man,
  mother: lone Woman
}

//A man has at most one wife
sig Man extends Person {
  wife: lone Woman
}

//A woman has at most one husband
sig Woman extends Person {
  husband: lone Man
}

//No one is his/her ancestor
fact {
  no p: Person | 
 	p  in p.^(mother + father)

  //Wife is transpose of husband
  wife = ~husband
}

assert noSelfFather {
	all m: Man | m = m.father
}

check noSelfFather
fun grandpas[p: Person] : set Person {
 	p.(mother + father).father
}

pred ownGrandpa[p: Person] {
 	p in grandpas[p]
}

run ownGrandpa for 4 Person
