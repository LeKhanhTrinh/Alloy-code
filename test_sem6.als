module test

sig Person{
	child: lone Person
}

fact{
	all x,y: Person |
		x != y 
		implies x.child != y.child
	all x,y: Person |
		x.child != y.child
		implies x != y
}

pred test1[x,y: Person]{
		x != y 
		implies x.child != y.child
}

run test1
