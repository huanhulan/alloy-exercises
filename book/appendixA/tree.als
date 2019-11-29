module appendixA/tree

pred isTree [r:univ->univ] {
	one root : univ {
    univ = root.*r
  }
	no n : univ | n in n.^r
	all n : univ | lone r.n
}

run isTree for 4
