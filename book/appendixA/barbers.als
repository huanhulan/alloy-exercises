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
pred paradox {
	some Barber
	}

run paradox for 100