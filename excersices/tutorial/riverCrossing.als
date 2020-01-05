open util/ordering[State]

abstract sig Object {
  eats: set Object
}

one sig Fox, Chicken, Farmer, Grain extends Object {}

/* Refinement */
fact {
  eats = Fox->Chicken + Chicken->Grain
}

/* State modeling */ 
sig State { near, far: set Object }

/* Everything is on one side of the river initially */
fact { first.near = Object && no first.far }

pred crossRiver [from, from', to, to': set Object] {
  one x: from | {
    from' = from - x - Farmer - from'.eats
    to' = to + x + Farmer
  }
}

/* crossRiver transitions between states */
fact {
  all s: State, s': s.next {
    Farmer in s.near =>
      crossRiver [s.near, s'.near, s.far, s'.far]
    else
      crossRiver [s.far, s'.far, s.near, s'.near]
  }
}

/* The farmer moves everything to the far side of the river. */
pred success { last.far=Object }

run success for 8