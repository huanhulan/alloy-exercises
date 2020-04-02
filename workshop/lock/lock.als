enum Digit { N0,N1,N2,N3,N4,N5,N6,N7,N8,N9 }
enum Code {d1,d2,d3}

abstract sig Lock {
   digits :  Code -> one Digit
}
one sig comb1, comb2, comb3, comb4, comb5, sol extends Lock {}

fact combinations {
    comb1.digits = d1->N6 + d2->N8 + d3->N2  // [6,8,2]
    comb2.digits = d1->N6 + d2->N1 + d3->N4  // [6,1,4]
    comb3.digits = d1->N2 + d2->N0 + d3->N6  // [2,0,6]
    comb4.digits = d1->N7 + d2->N3 + d3->N8  // [7,3,8]
    comb5.digits = d1->N7 + d2->N8 + d3->N0  // [7,8,0]
}

fact solution {
  one comb1.digits & sol.digits // one digit placed correctly
  
  no comb2.digits & sol.digits // no correctly placed digits
  one univ.(comb2.digits) & univ.(sol.digits) // one correct digit
  
  no comb3.digits & sol.digits // no correctly placed digits
  # ( univ.(comb3.digits) & univ.(sol.digits) ) = 2 // two correct digits
  
  no  univ.(comb4.digits) & univ.(sol.digits) // no correct digit
  
  no comb5.digits & sol.digits // no correctly placed digits
  one univ.(comb5.digits) & univ.(sol.digits) // one correct digit
}

run {}