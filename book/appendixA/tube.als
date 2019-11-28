/*
 * Adapted from Exercise A.1.11 on page 236 of
 * Software Abstractions, by Daniel Jackson
 *
 * In this exercise, you'll write some constraints about a simplified version
 * of the railway lines of the London Underground, or "tube". (You can find the
 * real thing at http://tube.tfl.gov.uk/.) There are three lines shown: the
 * Jubilee line running north to south from Stanmore; the Central line running
 * west to east to Epping; and the Circle line running clockwise through Baker
 * Street.
 *
 * A simplified portion of the tube is shown below
 *
 *               Stanmore
 *             x
 *             |
 *             | Baker Street
 *           - x -
 *         /   |   \
 *        /    |    \
 *       |     |     |         Epping
 *  -----------------|-------x
 *       |     |     |
 *        \    |    /
 *         \   |   /
 *           -----
 *             |
 *             |
 *
 * You are given the following relations:
 *
 *  - Station:
 *    the set of all stations
 *
 *  - JubileeStation, CentralStation, CircleStation:
 *    for each line, a subset of Station
 *
 *  - jubliee, central, circle:
 *    binary relations relating stations on each line to one another if they
 *    are directly connected
 *
 *  - Stanmore, BakerStreet, Epping
 *    singleton subsets of Station for individual stations
 */

module appendixA/tube

abstract sig Station {
}

sig JubileeStation in Station {
  jubilee: set JubileeStation
}

sig CentralStation in Station {
  central: set CentralStation
}

sig CircleStation in Station {
  circle: set CircleStation
}

one sig
	Stanmore, BakerStreet, BondStreet, Westminster, Waterloo,
	WestRuislip, EalingBroadway, NorthActon, NottingHillGate,
	LiverpoolStreet, Epping
	extends Station {}

/*
* Mathematical definition of a total set
*/
pred line [totalSet:Station, relation: Station->Station] {
	no ^relation & iden
	all node:totalSet | lone node.relation // because the terminal object doesn't have a successor
	all disj node, node': totalSet{
		one ((node->node' + node'->node) & ^relation)
	}
}

/*
* Mathematical definition of a circle graph
*/
pred circle[circleSet:Station, circleRelation: Station->Station] {
		no circleRelation & iden
		all node:circleSet | one node.circleRelation
		all node: circleSet {
		circleSet in node.^circleRelation
	}
}

/*
* (a) Station S is served by line L1 but not by line L2
*/
fact reachableOnlyBy1Line{
	(Stanmore + Waterloo) = ((JubileeStation - CircleStation) - CentralStation)

	(WestRuislip + EalingBroadway + NorthActon + Epping) = ((CentralStation - JubileeStation) - CircleStation)
}

/*
* (b) line L forms a circle
*/
fact circleLine {
	(
		BakerStreet + NottingHillGate
		+ Westminster + LiverpoolStreet
	) = CircleStation
	circle[CircleStation, circle]
}

/*
* (c) line L forms a strait line
*/
fact straitLine {
	(Stanmore+BakerStreet+BondStreet+Westminster+Waterloo) = JubileeStation
	line[JubileeStation, jubilee]
	no jubilee.Stanmore
	no Waterloo.jubilee
}

/*
* (d) Line L is a straight line, until it branches into two straights at station S
* (g) Two branches merge into one
*/
fact branch {
	(
		WestRuislip + 
		EalingBroadway + 
		NorthActon + 
		NottingHillGate +
		BondStreet +
		LiverpoolStreet +
		Epping
	) = CentralStation
	no central & iden
	line[CentralStation - EalingBroadway, central - (EalingBroadway->NorthActon)]
	line[CentralStation - WestRuislip, central - (WestRuislip->NorthActon)]

	no (WestRuislip->EalingBroadway) & ^central
	no (EalingBroadway->WestRuislip) & ^central
	(WestRuislip+EalingBroadway)->NorthActon in central
}

/*
* (e) The ends of line L are stations S1 and S2
*/
fact endOfLines {
	// for jubilee
	no jubilee.Stanmore
	no Waterloo.jubilee

	// for central
	no central.WestRuislip
	no central.EalingBroadway
	no Epping.central
}

/*
* (f) It's possible to travel from station S1 to station S2 on line L
*/
fact travelable {
	BakerStreet.circle = NottingHillGate
	NottingHillGate.central = BondStreet
	BakerStreet.jubilee = BondStreet
	Stanmore.jubilee = BakerStreet
	LiverpoolStreet.central = Epping
}

/*
* (h) If you get on an L line train at station S1, you will eventually reach station S2
*/
fact reachableByTransfering{
	all station:CircleStation {
		(BondStreet + LiverpoolStreet + Epping) in (station.^circle.^central)
		(BondStreet + Westminster + Waterloo) in (station.^circle.^jubilee)
	}
}

pred show {}

run show

/*
* Check the shape
*/
check {
	#circle = 4
	#jubilee=4
	#central=6
}
