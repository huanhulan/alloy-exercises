sig State {
  succesor: set State
}

abstract sig StateMachine {
  initialState: some State,
  state: some State
} {
  initialState in state
}

/*
* (a) a deterministic machine, in which each state has at most one successor;
*/
pred determnstic[m: StateMachine] {
  all s: m.state |
    #s.succesor < 2
}

/*
* (b) a nondeterministic machine, in which some states have more than
* one successor;
*/
pred nondetermnstic[m: StateMachine] {
  some s: m.state |
    #s.succesor > 1
}

/*
* (c) a machine with unreachable states;
*/
pred unreachable[m: StateMachine] {
  some s: m.state |
    s not in m.initialState.*succesor
}

pred reachable[m: StateMachine, s: State] {
  s in m.initialState.*succesor
}

/*
* (d) a machine without unreachable states;
*/
pred allReachable[m: StateMachine] {
  all s: m.state | reachable[m, s]
}

/*
* (e) a connected machine in which every state is reachable from every
* other state;
*/
pred connected[m: StateMachine] {
  allReachable[m]
  and
  all disj s, s': m.state |
    s' in s.~succesor
}

/*
* (f) a machine with a deadlock: a reachable state that has no successors;
*/
pred deadlock[m: StateMachine] {
  some s: m.state {
    reachable[m, s]
    and
    no s.succesor
  }
}

/*
* (g) a machine with a livelock: the possibility of an infnite execution in 
* which a state that is always reachable is never reached.
*/
pred livelock[m: StateMachine] {
  some s: m.state {
    reachable[m, s]
    and
    some i: m.initialState | s not in i.*succesor
  }
}

// every state belones to at least one state machine
fact noLeakStates {
  all s: State |
    state.s != none
}

fact {
  all s: State |
    let m = state.s |
      state.(s.*succesor) = m

  all disj m, m': StateMachine |
    no m.state & m'.state
}