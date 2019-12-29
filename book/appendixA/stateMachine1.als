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
  succesor: disj some State
}

abstract sig StateMachine {
  states: disj some State,
  initialState: disj some State,
  transitionLabels: disj some String,
  transition: String -> State -> State,
  traceLables: disj some String,
  traces: traceLables one -> (seq transitionLabels),
} {

  initialState in states

  no disj l,l': transitionLabels | transition[l] = transition[l']
  // no leaky states within an state machine
  // and
  // transition is just an syncronym of succesor
  all transitionLabel: transitionLabels {
    let transition = transition[transitionLabel] {
      #transition = 1
      and
      #State.transition = 1
      and
      #transition.State = 1
    }
  }

  transition.State.State in transitionLabels
  and
  all s: states | s.*succesor in states

  reachable[this]
  and
  states <: succesor = transition[transitionLabels]

  no traceLables & transitionLabels
  and
  // all trace are different
  no disj traceLable,traceLable': traceLables| traces[traceLable] = traces[traceLable']

  all traceLabel: traceLables |
    let trace = traces[traceLabel] {
      #trace > 1 => {
        noDuplicates[trace]
        // all trace begin with an intial state
        let firstTransLabel = trace[0] {
          let firstTransition = transition[firstTransLabel] {
            firstTransition.State in initialState
          }
        }
        // and follow the rule of compositionality
        all idx: trace.inds - trace.lastIdx |
          let nextIdx = idx.next |
            let f = transition[trace[idx]] |
              let g = transition[trace[nextIdx]] {
                f[State] = g.State
              }
      }
    }
}

sig Simulation {
  domain, codomain: StateMachine,
  r: State -> State
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

pred reachable[m: StateMachine] {
  some i: m.initialState |
    all s: m.states - m.initialState |
      s in i.^succesor
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
  and
  some m: StateMachine|
    #m.initialState < #m.states
} for 3 but exactly 5 State, exactly 7 String, 3 seq

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