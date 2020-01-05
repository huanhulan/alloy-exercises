module appendixA/riverCrossing
open util/ordering[State]

abstract sig Cargo { eats: set Cargo }

sig State {
  here, there: set Cargo
}

one sig Farmer, Goat, Cabbage, Wolf extends Cargo {}

fact foodChain {
  (Goat->Cabbage + Wolf->Goat) = eats
}

pred crossRiver[
  from, from',
  to, to': set Cargo
] {
  one x: from |
    from' = (from - x - Farmer) - from'.eats
    and
    to'= to + x + Farmer
}

fact inv {
  first.here = Cargo
  first.there = none
}


fact strategy {
  all state: State, state': state.next {
    Farmer in state.here =>
      crossRiver[state.here, state'.here, state.there, state'.there]
    else
      crossRiver[state.there, state'.there, state.here, state'.here]
  }
}

pred success {
  last.here = none
  last.there = Cargo
}

run success for 8 State
