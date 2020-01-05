module appendixA/barbers

sig Man { shaves: set Man }

sig Barber extends Man { }

fact {
	Barber.shaves = { m: Man | m not in m.shaves }
	}

pred noBarber {
	no Barber
	}

run noBarber for 3