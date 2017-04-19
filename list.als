sig Elt {}
sig List {}

sig NonEmptyList extends List {next: List, elt: Elt}

fact {all p: List | p !in p.^next}

fun cons (after: List, e: Elt): List {
	after.next = before
	after.elt = e
}

fun car (before: List, e: Elt) : List{
	e = before.elt
}

assert GetBack {all p: List, e: Elt | car(cons (p,e)) = e}
