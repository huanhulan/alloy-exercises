module appendixA/barbers

abstract sig Human { shaves: set Man }

/*
* Solving the paradox by introducing the existence of women
*/
sig Man, Woman extends Human {}

one sig Barber in Human { }

fact {
	Barber.shaves = { m: Man | m not in m.shaves }
	}

pred BarberShavesHimself {
	Barber in Barber.shaves
	}

pred BarberNotShavesHimself {
	Barber ! in Barber.shaves
	}

// No instance found. Predicate may be inconsistent.
pred NoParadox {
	BarberNotShavesHimself or BarberShavesHimself
	}

run NoParadox