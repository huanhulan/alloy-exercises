abstract sig Achievement {}

sig Man {
  floor: one Floor,
  ceiling: one Ceiling
}

sig Floor, Ceiling in Achievement {}

/*
* One man’s ceiling is another man’s floor.
*/
pred ceilingIsFloor {
  all disj m, m': Man |
    m.ceiling = m'.floor
}

fact {
  #Man>1
}

/*
* Does this imply that one man’s floor is another man’s ceiling?
*/
check {
  ceilingIsFloor => all disj m, m': Man | m.floor = m'.ceiling
}
