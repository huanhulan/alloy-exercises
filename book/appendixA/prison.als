module appendixA/prison

sig Gang { members: set Inmate }

sig Inmate { room: Cell }

sig Cell { }

/*
* (a)  Write a new predicate called safe, saying that the assignment must avoid placing two inmates in the same cell if they are members of different gangs
*/
pred safe {
		all disj gang, gang' : Gang, 
			gangsters: gang.members, 
			gangsters': gang'.members | gangsters.room != gangsters'.room
	}

/*
* (b) Write a new predicate called happy, saying that gang members only
share cells with members of the same gang.
*/
pred happy {
	all gang: Gang | no gang.members.room & (Inmate - gang.members).room 
}

pred show {
	// your constraints should go here
	}

fact rulesOfGang {
	all disj gang, gang': Gang | no (gang.members & gang'.members)
	no gang:Gang | no gang.members
}

fact "each and every prisoner belongs to a cell" {
	all prisoner: Inmate | one prisoner.room
}

run show for 3 but exactly 2 Gang, exactly 4 Inmate
run happy for 3 but exactly 2 Gang, exactly 4 Inmate
run safe for 3 but exactly 2 Gang, exactly 4 Inmate

/*
* (b) A safe assignment is not neccesary a happy assinment
*/
check {
	safe => happy
}

/*
* (c)  Add a constraint as a fact that ensures that safety will indeed imply happiness.
*/
// fact safe2Happy {
// 	safe => happy
// }