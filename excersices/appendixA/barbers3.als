module appendixA/barbers

sig Man { shaves: set Man }

sig Barber extends Man { }

fact {
	Barber.shaves = { m: Man | m not in m.shaves }
	}

pred someBarber {
	#Barber>1
	}

run someBarber for 5