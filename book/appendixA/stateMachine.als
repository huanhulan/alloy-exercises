open lib/stateMachine


one sig M1 extends StateMachine{}

run { determnstic[M1] }
run { nondetermnstic[M1] }
run { unreachable[M1] }
run { allReachable[M1] }
run { connected[M1] }
run { deadlock[M1] }
run {
  livelock[M1]
}