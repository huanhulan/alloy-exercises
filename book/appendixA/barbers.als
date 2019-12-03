module appendixA/barbers

sig Man { shaves: set Man }

one sig Barber extends Man { }

fact {
	Barber.shaves = { m: Man | m not in m.shaves }
	}


// pred BarberShavesHimself {
// 	Barber in Barber.shaves
// 	}

// pred BarberNotShavesHimself {
// 	Barber ! in Barber.shaves
// 	}

// No instance found. Predicate may be inconsistent.
pred Paradox {
	some Barber
	}

run Paradox for 100