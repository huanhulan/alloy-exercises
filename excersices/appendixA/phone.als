module appendixA/phones

sig Phone {
	requests: set Phone,
	connects: lone Phone,
	forward: lone Phone,
}

fact {
	all p :Phone, q: p.connects | (p.requests = q && no q.forward) || (p.requests.forward = q)

	~connects.connects in iden
	connects.~connects in iden

	all p : Phone, q : p.connects | no q.connects
	no ~connects & connects

	~forward.forward in iden
	forward.~forward in iden
	all p : Phone, q : p.forward | no q.forward
	no ~forward & forward


	no forward & requests


	no iden & requests
  no iden & connects
	no iden & forward
}

pred show {
	some connects
	some requests
	some forward
}

run show for exactly 4 Phone