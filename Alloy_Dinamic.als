module example/tutorial/Map

abstract sig Object{}

//Object can either be Keys or Value, but not both
sig Key, Value extends Object{}

sig Map{values: Key -> lone Value}

pred show(){}

assert mappingIsUnique{
	all m:Map, k:Key, v, v':Value |
		k -> v in m.values and
		k -> v' in m.values 
		implies v = v'
}

assert putLocal {
	all m, m' : Map, k, k':Key, v:Value |
	put[m,m',k,v] and k != k' implies
		lookup[m,k'] = lookup[m',k']
}

fact{
	all k:Key | some v:Value, m:Map | k->v in m.values
	all v:Value | some k:Key, m:Map | k->v in m.values
}

pred put(m,m': Map, k:Key, v:Value){
	m'.values = m.values + k -> v
}

check putLocal 
//check mappingIsUnique for 2
run put for 3 but exactly 2 Map, exactly 1 Key, exactly 1 Value
