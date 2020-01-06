open util/time
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
  no Event.post & T0/first
  all disj e,e': Event {
    no e.pre & e'.pre
  }
  all t: Time - T0/last |
    let t' = t.next |
      some e: Event { 
        e.pre = t 
        e.post = t'
      }
}

/*
* determine whether there is cached version of wanted 'Type' of asset in 'S3' under given 'Time'
*/
pred inS3[type: Type, t: Time] {

}

/*
* request: if 'param' is represented, filter corresponding resource from 'Cloudfront', otherwise from 'S3',
* if fetching from 'Cloudfront', always return the 'max' version of the type.
*/
fun request[type: Type, param: Int]: set Asset {

}

/*
* 'Build' Event: represented by its 'BuildVersion', producing new 'Entry' and its 'Other' assets.
* Also push its assets into 'Cloudfront' while has no effect on other elements.
*/
sig Build extends Event{
  v: disj BuildVersion
}{

}

fun build[a: Asset, t:Type, v: BuildVersion]: Asset {

}


/*
* 'Load' Event: issue 2 'request's, one for entry with 'Int' param, the other for 'Other' without param.
* And if some fetched resources can't be found in current 'S3', then put resources into the 'next' state of 'S3'.
* Storing the returning assets into event's 'response' filed.
*/
sig Load extends Event{
  response: set Asset
}{

}

/*
* check: for evey 'Load' event, its assets' versions are the same
*/

