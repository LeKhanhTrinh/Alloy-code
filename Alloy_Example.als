module examples/tutorial/Queue

// sig = vocabulary of model ~ class
// lone = alone ~ pointer
sig Queue {root: lone Node} //each Queue has no more than one root
sig Node {next: lone Node}  //each Node has no more than one next

// fact is the constraint for models
fact nextNotReflexive {no n:Node | n = n.next} 	//a node cannot point to itself
fact allNodesBelongToSomeQueue{
	//for all node "n" and some queue q, the sequence format is q.root.*next
	all n:Node | one q:Queue | n in q.root.*next
}
fact nextNotCyclic{
	no n:Node | n in n.^next
}

//pred = predicate ~ function
// Alloy produce instance that satisfy the pred
// is similar to finding models of a given schema

pred show(){}

// set at most 2 objects in each sig and return a smaller instance
run show for 3
