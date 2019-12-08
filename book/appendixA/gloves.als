/*
* A surgeon must operate on three patients, but has only two pairs of gloves.
* There must be no cross contamination: 
*    the surgeon must not come into contact with the blood of any patient,
*    and no patient must come into contact with the blood of another patient. 
* The surgeon needs two hands to work.
* How does she do it? 
*/

module exercises/gloves

open util/ordering[Time] as T0
open util/boolean
open util/integer

sig Time{}

sig GloveSide {
  // sides can get contaminated over time
  contaminated: Bool -> Time
} {
  all t: Time |
      contaminated.t = False
      or
      contaminated.t = True
  // once contaminated always contaminated
  all t: Time - T0/last |
    let t' = t.next |
      contaminated.t = True => contaminated.t' = True
}

sig Glove {
  // sides can change over time
  inner: GloveSide -> Time, -- the side toward the doctor
  outer: GloveSide -> Time -- the side toward patients
} {
  all t: Time |
    #inner.t = 1
    and
    #outer.t = 1
    and
    inner.t != outer.t

  // each glove's side can be flipped
  all t: Time - T0/last |
    let t' = t.next |
      (inner+outer).t = (inner+outer).t'
}

sig Patient{}

one sig Doctor {
  // doctor can change gloves over time
  // the [0] index is the glove that touches one of her hands
  leftHand: (seq Glove) -> Time,
  rightHand: (seq Glove) -> Time
} {
  all t:Time {
      // one glove can only fit one hand
      no leftHand.t.elems & rightHand.t.elems
      // The doctor can't copy gloves on her hands
      all disj i,i': (leftHand.t).inds |
          leftHand.t[i] != leftHand.t[i']
      all disj i,i': (rightHand.t).inds |
          rightHand.t[i] != rightHand.t[i']

      // The doctor must not come into contact with any patient's blood
      all glove: (leftHand+rightHand).t[0] |
        glove.inner.t.contaminated.t = False
  }
}

abstract sig Event {
  // pre- and post-state times for- this event
  pre, post: one Time
}

sig Operate extends Event {
  patient: one Patient
}{
  // precondition: clean gloves
  all doc: Doctor {
    // 1st. must put on gloves
    #doc.leftHand.pre.elems>0 and #doc.rightHand.pre.elems>0
    and
    {
      // 2nd. if only one glove on each hand, the both gloves must be clean on all 4 sides
      (#doc.(leftHand+rightHand).pre.elems = 2) => {
        all glove: doc.(leftHand+rightHand).pre[0] |
          (glove.outer.pre -> False -> pre)
           in contaminated
      }
    }
    and
    // 3. the glove's outer side that touches the patient must be clean
    all lastGlove: (doc.(leftHand+rightHand).pre).last |
      lastGlove.outer.pre -> False -> pre in contaminated
  }


  // postcondition: outer gloves not clean, everything else stays the same
  let doc = Doctor {
    // 1st. glove sequences stay the same
    doc.leftHand.post = doc.leftHand.pre
    and
    doc.rightHand.post = doc.rightHand.pre

    // 2st. during a surgery, no glove changes its state
    all g:Glove|
      g.inner.pre = g.inner.post
      and
      g.outer.pre = g.outer.post

    // 3rd. last glove's outer-side would be contaminated
    doc.leftHand.pre.last.outer.pre->True->post in contaminated
    doc.rightHand.pre.last.outer.pre->True->post in contaminated
    all s:(GloveSide - doc.leftHand.pre.last.outer.pre - doc.rightHand.pre.last.outer.pre) | s.contaminated.pre = s.contaminated.post
  }
}

sig TakeGlovesOff extends Event {
  glove: one Glove
} {
  (
    glove in ((Doctor.leftHand + Doctor.rightHand).pre).last
    and
    glove not in ((Doctor.leftHand + Doctor.rightHand).post).elems
  )
  and
  {
    (glove = Doctor.leftHand.pre.last) => {
      Doctor.rightHand.pre = Doctor.rightHand.post
      and
      Doctor.leftHand.pre.butlast = Doctor.leftHand.post
    }
    else
      Doctor.leftHand.pre = Doctor.leftHand.post
      and
      Doctor.rightHand.pre.butlast = Doctor.rightHand.post
  }
}

sig PutGlovesOn extends Event {
  glove: one Glove
} {
  (
    glove not in ((Doctor.leftHand + Doctor.rightHand).pre).elems
    and
    glove in ((Doctor.leftHand + Doctor.rightHand).post).last
  )
  and
  {
    (glove = Doctor.leftHand.post.last) => {
      Doctor.rightHand.pre = Doctor.rightHand.post
      and
      Doctor.leftHand.post.butlast = Doctor.leftHand.pre
    }
    else
      Doctor.leftHand.pre = Doctor.leftHand.post
      and
      Doctor.rightHand.post.butlast = Doctor.rightHand.pre
  }
}

fact transitions {
  all t: Time - T0/last |
    let t' = t.next |
      some e: Event { 
        e.pre = t 
        e.post = t'

        // doctor can't change the amount of gloves on her hand without put on/take off action
        let doc = Doctor {
          (
            sub[#doc.leftHand.t', #doc.leftHand.t] = 1
            or
            sub[#doc.rightHand.t', #doc.rightHand.t] = 1
          ) => e in PutGlovesOn
          else
          (
            sub[#doc.leftHand.t, #doc.leftHand.t'] = 1
            or
            sub[#doc.rightHand.t, #doc.rightHand.t'] = 1
          ) => e in TakeGlovesOff
        }

        all gs: GloveSide {
          gs.contaminated.t' != gs.contaminated.t => e in Operate
        }
      }
  no t: Time - T0/last |
      let t' = t.next |
        let doc = Doctor {
          sub[#doc.leftHand.t', #doc.leftHand.t] > 1
          or
          sub[#doc.rightHand.t', #doc.rightHand.t] > 1
        }
}

fact inv {
  // all gloves are clean initially
  all s: GloveSide | s.contaminated.T0/first = False
  all doc: Doctor |
    doc.leftHand.T0/first.elems = none
    and
    doc.rightHand.T0/first.elems = none
  no Event.post & T0/first
}

fact glove {
  #GloveSide = mul[#Glove, 2]
  
  // each glove side always belongs to only one glove
  all disj g,g': Glove |
    all t: Time |
      no g.inner.t & g'.inner.t
      and
      no g.outer.t & g'.outer.t
      and
      no g.outer.t & g'.inner.t
}

// sequential
fact oneEventTime {
  // one operation at a time
  all disj e,e': Event {
    no e.pre & e'.pre
  }
  all disj o,o': Operate {
    no o.patient & o'.patient
  }
}

fact crossContamination {
  all t: Time - T0/last |
     let t' = t.next |
      let doc = Doctor |
        let golves = doc.(leftHand+rightHand).t |
          all disj i, i': golves.inds |
            ( 
              #golves>1
              and
              i'>i
              and
              i'-i=1
              and
              golves[i].outer.t.contaminated.t = True
            ) => {
              golves[i'].inner.t'.contaminated.t' = True
            }
}

run {
  #Operate = #Patient
} for 10 but exactly 4 Glove, exactly 3 Patient, 4 seq, exactly 11 Time