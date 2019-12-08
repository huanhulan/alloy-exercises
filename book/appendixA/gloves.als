/*
* A surgeon must operate on three patients, but has only two pairs of gloves.
* There must be no cross contamination: 
*    the surgeon must not come into contact with the blood of any patient,
*    and no patient must come into contact with the blood of another patient. 
* The surgeon needs two hands to work.
* How does she do it? 
*/

module exercises/gloves

open util/ordering[Time] as T0
open util/boolean

sig Time{}

sig GloveSide {
  // sides can get contaminated over time
  contaminated: Bool -> Time
} 

sig Glove {
  // sides can change over time
  inner: GloveSide -> Time,
  outer: GloveSide -> Time
}

sig Patient{}

one sig Doctor {
  // doctor can change gloves over time
  leftHand: (seq Glove) -> Time,
  rightHand: (seq Glove) -> Time
} 

abstract sig Event {
  // pre- and post-state times for- this event
  pre, post: one Time
}

sig Operate extends Event {
  patient: one Patient
}{
  // precondition: clean gloves
  // ...

  // postcondition: outer gloves not clean, everything else stays the same
  // ...
}

sig TakeGlovesOff extends Event {
} {
  // ...
}

sig PutGlovesOn extends Event {
} {
  // ...
}

fact transitions {
  all t: Time - T0/last |
    let t' = t.next |
      some e: Event { 
        e.pre = t 
        e.post = t'
      }
}

fact inv {
  no contaminated.T0/first
}

run {
  // all three patients operated
} for 7 but exactly 2 Glove, exactly 4 GloveSide, exactly 3 Patient, 5 Int