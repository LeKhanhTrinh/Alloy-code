module test1

sig Element{}
sig Bool{}
sig BStackInt extends Element{
	push: Int -> lone BStackInt,
	peek: lone Int,
	pop: lone BStackInt,
	size: one Int,
	empty: one Bool,
	maxSize: one Int
}

one sig start{
	make: Int -> lone BStackInt,
	pushInt0: set Int,
	makeInt0: set Int
} 

fact BStackIntConstruction{
	BStackInt in
	(start.make[Int]).*
	{x:BStackInt, y:x.push[Int]}
}

fact ElementUsedVariables {
	Element in (BStackInt)
}

fact axiomBStackInt1{
	all E:Int, S:BStackInt |
	(E in start.pushInt0) implies (
	(S.size < S.maxSize) implies (S.push[E].pop = S))
}

fact domainBStackInt2{
	all E:Int, S:BStackInt |
	(S.size < S.maxSize and E in start.pushInt0)
	implies one S.push[E] else no S.push[E]
}

run run_axiomBStackInt4_1{
	some S: BStackInt |
	(S.empty = Bool) and (S.size != 0)
} for 7

run run_axiomBStackInt4_0{
	some S: BStackInt |
	(S.empty = Bool) and (S.size = 0)
} for 7

