/*
* (a) Model the track layout as a collection Segment of track segments,
* with a relation next from Segment to Segment. 
* Segments are physically disjoint, touching each other only at their endpoints,
* and are direc- tional, with trains assumed to travel from one endpoint to the other.
* The endpoints are not represented explicitly, though. 
* Instead, we are representing the connection of the exit end of s1 to the entrance end of s2 
* by next mapping s1 to s2. 
* Generate some sample layouts, and obtain some nice visualizations using the Alloy Analyzer.
*/
sig Segment{
  next, overlaps: set Segment
}{
  this not in next --non-reflexitive
  this in overlaps --reflexitive
}

/*
* (b) To model the possibility of collision, we might just say that two trains can collide
* only when they are on the same segment. For a more general notion,
* which allows for the possibility of a collision between trains on segments that are,
* for example, parallel to each other, we can declare a relation overlaps that represents,
* very ab- stractly, the physical layout of the track, mapping a segment s1 to a segment s2 
* when it would be dangerous for one train to be on s1 and another to be on s2 at the same time.
*/
fact selfOverlapping{
  ~overlaps in overlaps --symmetic
}

sig Train {}

/*
* (c) Declare a signature Train to represent a set of trains, and a signature 'TrainState',
* with a relation on from Train to Segment to represent their positions.(Remember that each train can occupy only a single segment.) 
* Define an additional feld 'occupied' in 'TrainState' that holds the set of segments occupied by trains.
* Generate and visualize some sample states; you’ll probably want to use coloring to indicate the occupied the segments.
*/
sig TrainState {
  on: Train -> lone Segment,
  occupied: set Segment
} {
  occupied = on[Train]
}


/*
* (d) To describe all physically possible train movements, introduce an
* operation on 'TrainState' that takes as arguments two train states
* (representing the pre- and poststates), and a set of trains that move,
* and constrains the train states so that, in this step, each train that
* moves passes from a segment to one of its successors under the
* next relation. Generate and visualize some sample executions of this
* operation.
*/
pred TrainsMove [currentState, nextState: TrainState, trainsOnRails: set Train] {
  all t: trainsOnRails | t.(nextState.on) in t.(currentState.on).next
  all t: Train - trainsOnRails | t.(nextState.on) = t.(currentState.on)
  }

/*
* To model the signaling system, introduce a signature 'GateState' with
* a feld 'closed' whose value is a set of segments, representing those
* segments beyond which a train is not supposed to travel. Note that
* there’s no need to introduce gates or lights as explicit atoms. Write
* a predicate that captures legal movements whose arguments are a
* 'GateState', a TrainState and a set of Trains that move.
*/
sig GateState {closed: set Segment}

pred GatePolicy [g: GateState, x: TrainState] {
  next.(x.occupied.overlaps) in g.closed
  all s1, s2: Segment | (some s1.next.overlaps & s2.next) => lone (s1+s2) - g.closed
}

/*
* (f) Write a safety condition on TrainState saying that trains never occupy overlapping segments,
* and generate some sample states that satisfy and violate the condition.
*/
pred Safe [x: TrainState] {all s: Segment | lone (x.on).(s.overlaps)}


/*
* (g) Write the policy as a predicate that takes as arguments a GateState and a TrainState.
* It may say, for example, that if several occupied segments share a successor, 
* then at most one can have an open gate
*/
assert PolicyWorks {
  all x, x': TrainState, g: GateState, ts: set Train |
    {
      TrainsMoveLegal[x, x', g, ts]
      Safe [x]
    } => Safe [x']
}

/*
* (h) write an assertion that says that when the trains move, if the mechanism obeys the gate policy,
* and the train movements are legal, then a collision does not occur (that is, the system does not 
* transition from a safe state to an unsafe state). Check this assertion, and if you fnd counterexamples,
* study them carefully, and adjust your model. Most likely, your gate policy will be at fault.
*/
pred MayMove [g: GateState, x: TrainState, ts: set Train] {
  no ts.(x.on) & g.closed
}

-- has counterexample in scope of 4
check PolicyWorks for 2 Train, 1 GateState, 2 TrainState, 4 Segment

pred TrainsMoveLegal [x, x': TrainState, g: GateState, ts: set Train] {
  TrainsMove [x, x', ts]
  MayMove [g, x, ts]
  GatePolicy [g, x]
}

// run TrainsMoveLegal for 3