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
  this not in next
  this in overlaps
}

/*
* (b) To model the possibility of collision, we might just say that two trains can collide
* only when they are on the same segment. For a more general notion,
* which allows for the possibility of a collision between trains on segments that are,
* for example, parallel to each other, we can declare a relation overlaps that represents,
* very ab- stractly, the physical layout of the track, mapping a segment s1 to a segment s2 
* when it would be dangerous for one train to be on s1 and another to be on s2 at the same time.
*/
fact {
  ~overlaps in overlaps
}

sig Train {}
sig TrainState {
  on: Train -> lone Segment,
  occupied: set Segment
} {
  occupied = on[Train]
}

run {} for 3