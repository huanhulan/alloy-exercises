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
  // this not in next --non-reflexitive
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

pred Safe [x: TrainState] {all s: Segment | lone ~(x.on)[s.overlaps]}

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

run Safe for 3