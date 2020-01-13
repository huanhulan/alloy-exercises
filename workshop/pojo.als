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

pred add [b, b': Object, n: Key, a: Value] {
	b'.mapping = b.mapping + n->a
}

pred del [b, b': Object, n: Key] {
	b'.mapping = b.mapping - n->Value
}

fun lookup [b: Object, n: Key] : set Value {
	n.(b.mapping)
}

assert delUndoesAdd {
	all b, b', b'': Object, n: Key, a: Value |
		add [b, b', n, a] and del [b', b'', n]
		implies
		b.mapping = b''.mapping
}

check delUndoesAdd for 3

assert addIdempotent {
	all b, b', b'': Object, n: Key, a: Value |
		add [b, b', n, a] and add [b', b'', n, a]
		implies
		b'.mapping = b''.mapping
}

check addIdempotent for 10