module examples/tutorial/Map
abstract sig Object {}

sig Key, Value extends Object {}

sig Map {
	values: Key -> lone Value
}

assert mappingIsUnique {
	all m:Map, k:Key, v, v’:Value |
	k -> v in m.values
	and k -> v’ in m.values
	implies v = v’
}

pred put(m, m’:Map, k:Key, v:Value) {
	m’.values = m.values + k -> v
}

assert putLocal { all m, m’: Map, k, k’: Key, v: Value |
	put[m,m’,k,v] and k != k’ implies
	lookup[m,k’] = lookup[m’,k’]
}

fun lookup(m: Map, k: Key): set Value k.(m.values)
