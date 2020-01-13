-- meta types
abstract sig Type {}
abstract sig JsString extends Type {}
abstract sig JsObject extends Type {}

-- instances
sig Key in JsString {}
sig Value in Type {}
sig Object in JsObject {
	mapping: Key -> lone Value
}

-- show some instances
run {} for 3

-- actions
pred add [o, o': Object, k: Key, v: Value] {
	o'.mapping = o.mapping + k->v
}

pred del [o, o': Object, k: Key] {
	o'.mapping = o.mapping - k->Value
}

fun lookup [o: Object, k: Key] : set Value {
	k.(o.mapping)
}

-- validation
assert addIdempotent {
	all o, o', o'': Object, k: Key, v: Value |
		add [o, o', k, v] and add [o', o'', k, v]
		implies
		o'.mapping = o''.mapping
}

check addIdempotent for 10

assert addLocal {
	all o, o': Object, k, k': Key, v: Value |
		add [o, o', k, v] and k != k'
		implies
		lookup [o, k'] = lookup [o', k']
}

check addLocal for 10

assert delUndoesAdd {
	all o, o', o'': Object, k: Key, v: Value |
		add [o, o', k, v] and del [o', o'', k]
		implies
		o.mapping = o''.mapping
}

check delUndoesAdd for 3
