/*
* Thanks to Peter Kriens for the solution:
* https://stackoverflow.com/a/59456058/8506808
*/
module austere_surgery

open util/relation
open util/ordering[Operation]

abstract sig Surface {}

abstract sig Human extends Surface {}
one sig Surgeon extends Human {}
sig Patient extends Human {}

sig Glove {
    inside   : disj Inside,
    outside  : disj Outside
} 
sig Inside, Outside extends Surface {}

sig Operation {
    patient       : disj Patient,
    -- surfaces is a path from surgeon -> glove* -> patient
    surfaces      : Surface -> lone Surface,
    gloves        : set Glove,
    contaminated  : Human-> Surface
} {
    -- constrain to be a proper path (could be improved)
    dom[surfaces] = Surgeon + (gloves.(inside+outside)-ran[surfaces])
    ran[surfaces] = patient + (gloves.(inside+outside)-dom[surfaces])
    all g : gloves | g.inside in dom[surfaces] iff g.outside in ran[surfaces]

    -- and no patient must come into contact with the blood of another patient. 
    surfaces.patient not in ran[contaminated - patient->Surface]

    -- the surgeon must not come into contact with the blood of any patient,
    Surgeon -> patient not in surfaces 
    Surgeon.surfaces not in Patient.contaminated
}

pred surgery {

    Surface = Glove.inside + Glove.outside + Human

    no first.contaminated

    all o' : Operation-first, o : o'.prev {

        o'.contaminated = o.contaminated 
            + o.touches[o.patient] 
            + o.touches[Surgeon]
            + o.touches[ran[o.contaminated-Surgeon->Surface]]   
    }
}

fun Operation.touches[ dirty : set Surface ] : (Patient+Surgeon)-> Surface {
    { from : dirty, to : Surface | from->to in this.surfaces or to->from in this.surfaces }
}


-- A surgeon must operate on three patients, but xe has only two pairs of gloves.
run surgery for 10 but exactly 3 Patient, exactly 3 Operation, exactly 2 Glove