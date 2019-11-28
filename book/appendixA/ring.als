module appendixA/ring

sig Node { next: set Node }

pred isRing {
	no Node<:next & iden
	all node:Node | one node.next
	all node: Node {
		Node in node.^next
	}
}

run isRing for exactly 4 Node
