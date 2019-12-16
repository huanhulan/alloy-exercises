/*
Consider two state machines M1 and M2 with labeled transitions. A relation r from the states of M1 to the states of M2 is a simulation of M1 in M2
if and only if
· whenever r relates a state s1 in M1 to a state s2 in M2, and M1 has a simulation labeled 'a' from s1 to s1’, M2 also has a simulation labeled a
from s2 to s2’ for some s2’ related by r to s1’, and
· whenever s1 is an initial state of M1, there is an initial state s2 of M2 where s1 and s2 are related by r

The relation r is a bisimulation if, in addition, ~r is a simulation of M2 in M1.
A trace of a state machine is a fnite sequence of simulation labels formed by starting in an initial state and following a path along transitions. The
behaviour of a machine can be described by the set of traces it exhibits.
(h) Construct an Alloy model of a state machine with traces, and simulation relations, and generate some examples of machines with their
associated trace sets.
(i) Add the notion of simulation, and generate some examples of machines related by simulations.
(j) If there is simulation between two machines, must they have the same trace set? Use Alloy to check this hypothesis. How about a bisimulation?
*/
sig State {
}

abstract sig StateMachine {
  states: some State,
  initialState: some State,
  transitionLabels: some String,
  transition: String -> State -> State,
  traceLables: some String,
  traces: traceLables one -> (seq transitionLabels),
} {
  all label: transitionLabels |
    // all transition happens within machine's states
    transition[label].State in states
    and
    transition[label][State] in states
    and
    // different transition has different labels
    #transition[label][State] = 1
    and
    #transition[label].State = 1

  no disj l,l': transitionLabels|
    transition[l] = transition[l']

  // all inital state has a transition
  some transition[transitionLabels][initialState]

  transition.State.State in transitionLabels
  initialState in states

  no traceLables & transitionLabels

  no disj l,l': traceLables|
    traces[l] = traces[l']

  all tl: traceLables |
    let trace = traces[tl] |
      let firstTransLabel = trace[0] |
        let firstTrans = transition[firstTransLabel] {
        #initialState.firstTrans >= 1
        and
        noDuplicates[trace]
        and
        all idx: trace.inds - trace.lastIdx |
          let next = idx.next |
            let curLabel = trace[idx] |
              let nextLabel = trace[next] |
                transition[curLabel][states] = transition[nextLabel].states
    }
}

sig Simulation {
  domain, codomain: StateMachine,
  r: State -> State
}

fact noCrossTransition {
  all disj m, m': StateMachine |
    no m.transitionLabels & m'.transitionLabels
}

fact noCrossStates {
  all disj m, m': StateMachine |
    no m.states & m'.states
}

fact noLeakStates {
  all s:State |
    one m: StateMachine |
      s in m.states
}

pred noDuplicates[trace: seq String] {
  all disj i,i': trace.inds |
      trace[i] != trace[i']
}


one sig M1 extends StateMachine{}
one sig M2 extends StateMachine{}

run {
  #M1.transitionLabels>1
  and
  #M2.transitionLabels>1
  and
  some m: StateMachine|
    some traces: m.traces|
      let traceLabel = m.traceLables |
        let trace = traces[traceLabel] |
          #trace.inds>=2
} for 3 but exactly 6 State, exactly 12 String, 5 seq

assert noCrossState {
  M1.transition[String].State not in M2.transition[String].State
  and
  M1.transition[String].State not in M2.transition[String][State]
  and
  M2.transition[String].State not in M1.transition[String].State
  and
  M2.transition[String].State not in M1.transition[String][State]
}

check noCrossState for 3 but exactly 6 State, exactly 12 String, 5 seq