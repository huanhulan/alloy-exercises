sig State {
  succesor: set State
}

one sig StateMachine {
  initialState: some State,
  state: some State
} {
  initialState in state
}

/*
* (a) a deterministic machine, in which each state has at most one successor;
*/
pred determnstic {
  all s: StateMachine.state |
    #s.succesor < 2
}

/*
* (b) a nondeterministic machine, in which some states have more than
* one successor;
*/
pred nondetermnstic {
  some s: StateMachine.state |
    #s.succesor > 1
}

/*
* (c) a machine with unreachable states;
*/
pred unreachable {
  some s: StateMachine.state |
    s not in StateMachine.initialState.*succesor
}

pred reachable[s: State] {
  s in StateMachine.initialState.*succesor
}

/*
* (d) a machine without unreachable states;
*/
pred allReachable {
  all s: StateMachine.state | reachable[s]
}

/*
* (e) a connected machine in which every state is reachable from every
* other state;
*/
pred connected {
  allReachable
  and
  all disj s, s': StateMachine.state |
    s' in s.~succesor
}

/*
* (f) a machine with a deadlock: a reachable state that has no successors;
*/
pred deadlock {
  some s: StateMachine.state {
    reachable[s]
    and
    no s.succesor
  }
}

/*
* (g) a machine with a livelock: the possibility of an infnite execution in 
* which a state that is always reachable is never reached.
*/
pred livelock {
  some s: StateMachine.state {
    reachable[s]
    and
    some i: StateMachine.initialState | s not in i.*succesor
  }
}

fact noLeakStates {
  all s: State |
    let StateMachine = StateMachine |
      StateMachine->s in state
}

run determnstic
run nondetermnstic
run unreachable
run allReachable
run connected
run deadlock
run livelock