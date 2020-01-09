open util/time as Time
open util/ordering[BuildVersion]
open util/integer

sig BuildVersion{}

abstract sig StaticFileService {
  assets: Time -> set Asset
}

one sig S3 extends StaticFileService{}
one sig Cloudfront extends StaticFileService{}

// empty uri&tag means that the asset has yet to be produced
abstract sig Asset{
  uri: lone Type,
  v: lone BuildVersion,
}

abstract sig Type {}
sig Entry extends Type{}
sig Other extends Type{}

abstract sig Event{
  pre, post: one Time
}

fact {
  no StaticFileService.assets[Time/first]
}

fact transitions {
  no Event.post & Time/first
  all t: Time - Time/last |
    let t' = t.next |
      some e: Event { 
        e.pre = t 
        e.post = t'
      }
  all disj e,e': Event {
    no e.pre & e'.pre
  }
}

/*
* determine whether there is cached version of wanted 'Type' of asset in a 'StaticFileService' under given 'Time'
*/
fun inService[type: Type, store: StaticFileService, t: Time]: set Asset {
  let matchedType = store.assets[t] | matchedType.uri & type
}

/*
* request: if 'urlParam' is represented, filter corresponding resource from 'Cloudfront',
* otherwise from 'S3',
* if fetching from 'Cloudfront', always return the 'max' version of the type.
*/
fun request[type: Type, t: Time, urlParam: Int]: set Asset {
  let f = inService[type, Cloudfront, t] |
    let f' = inService[type, S3, t] {
      urlParam != none => f' else {
        f != none => f
        else
        f'
      }
    } 
}

/*
* 'Build' Event: represented by its 'BuildVersion', producing new 'Entry' and its 'Other' assets,
* and 'BuildVersion' increments by each 'Build'.
* Also push its assets into 'S3' while has no effect on other elements.
* If the name is the same, Overwrite the file
* every 'Asset' belongs to one dist of a 'Build'
*/
sig Build extends Event{
  v: disj BuildVersion,
  dist: disj set Asset
}{
  dist.v = v
  #dist = 2
  all disj e,o: dist | e.uri != o.uri
}

fact {
  Asset = Build.dist
}

fun build[a: Asset, t:Type, v: BuildVersion]: Asset {

}


/*
* 'Request' Event: issue 2 'request's, one for entry with 'Int' param, the other for 'Other' without param.
* And if some fetched resources can't be found in current 'S3', then put resources into the 'next' state of 'S3'.
* Storing the returning assets into event's 'response' filed.
*/
sig Request extends Event{
  response: set Asset
}{

}

/*
* check: for evey 'Request' event, its assets' versions are the same
* and each 'Request' always receive the newest version of assets.
*/

