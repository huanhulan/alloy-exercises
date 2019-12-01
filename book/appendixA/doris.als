module appendixA/doris

sig People {
  loves: People
}

one sig Me, MyBabe in People {}

pred iLoveMyBabe {
    /* every body loves my baby */
    -- let everyBody = People | // from a strict logic point of view  (1)
    let everyBody = (People - MyBabe) | // (2)
      everyBody !=none <=> everyBody.loves = MyBabe
    and
    /* but my baby don't love nobody but me */
    MyBabe.loves = Me
}

fact {
  some People
  one MyBabe
  one Me
}

// pred iAmMyBabe {
//   Me=MyBabe
// }

run iLoveMyBabe for exactly 5 People

// if comment (2), then no counterexample would be found
check {
  iLoveMyBabe => (Me = MyBabe)
}