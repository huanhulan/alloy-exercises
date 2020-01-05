/*
* Alice and Bob are couples, they recently attended a party at which there were four other married couples.
* Various handshakes took place:
*   No one shook hands with oneself, nor with one's spouse;
*   and no one shook hands with the same person more than once.
* After all the handshakes were over, Alice asked each person, including my wife, how many hands he (or she) had shaken. 
* Each gave her a different answer.
* How many hands did my wife shake?
*/

module exercises/handshake

sig People {
  handshake: set People,
  spouse: one People
}

one sig Alice, Bob in People {}

fact spouse {
  no iden & spouse
  ~spouse in spouse
}

fact hosts {
  Alice.spouse = Bob
}

fact handshakeRules {
  no iden & handshake
  no p: People | p.spouse in p.handshake
  ~handshake in handshake
  // all p:People {
  //   (some p.handshake implies {
  //     all q: p.handshake |
  //       p in q.handshake
  //   }
  //   or
  //   p.handshake = none)
  // }
}

pred answersForAlice {
  all disj p, q: People - Alice |
    #p.handshake != #q.handshake
}

run answersForAlice for exactly 4 People
run answersForAlice for exactly 6 People
/*
* Need to config the alloy to get the answer:
* * Option [Prevent overflows] changed to [false] -- most important
* * Option [Maximum memory] changed to [256]
* * Option [Maximum stack] changed to [1024]
* * Option [Solver] changed to [sat4j]
* * Option [SkolemDepth] changed to [1]
*/
run answersForAlice for exactly 10 People

// Might there be another solution? 
check {
  answersForAlice=>#Bob.handshake = 4
} for exactly 10 People