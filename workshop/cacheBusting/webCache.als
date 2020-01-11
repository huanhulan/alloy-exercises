open util/time as Time
open util/ordering[BuildVersion]
open util/integer

sig BuildVersion {}

abstract sig StaticFileService {
  assets: Time -> set Asset
}

one sig S3 extends StaticFileService {}
one sig Cloudfront extends StaticFileService {}

-- no need for modeling the client-side cache since caching on client side can be easily detected/eluded

abstract sig Asset {
  uri: one Type,
  v: one BuildVersion,
}

/*
* Since we have two type of assets, it doesn't matter wether the type is String or not,
* any type of 2 are isomorphic.
*/
abstract sig Type {}
one sig Entry extends Type {}
one sig Other extends Type {}

abstract sig Event {
  pre, post: one Time
}

/*
* 'Build' Event: represented by its 'BuildVersion', producing new 'Entry' and its 'Other' assets,
* and 'BuildVersion' increments by each 'Build'.
* Also push its assets into 'S3' while has no effects on other elements.(TODO)
* If the name is the same, Overwrite the file
* every 'Asset' belongs to one dist of a 'Build'
*/
sig Build extends Event {
  v: disj BuildVersion,
  dist: disj set Asset
}{
  // rules for its assets
  dist.v = v
  #dist = 2
  all disj e,o: dist | e.uri != o.uri

  // rules for S3
  pushToS3[dist, pre, post]
}

/*
* 'Request' Event: issue 2 'request's, one for entry with 'Int' param, the other for 'Other' without param.
* And if some fetched resources can't be found in current 'S3', then put resources into the 'next' state of 'S3'.
* Storing the returning assets into event's 'response' filed.
*/
sig Request extends Event {
  response: set Asset
}{
  /*
  * For this version, when a browser receives our html file, it would always issue an http request for
  * index.js with an 'timestamp' query param whose value are the timestamp when the request get received by
  * the server. And for the other static files will always use the same file name without any query param.
  * So modeling the server who generates html files is just **isomorphic** to the following way: 
  * modeling every request/response pair of a single page rendering
  */ 
  response = request[Entry, pre, Int] + request[Other, pre, none]
  cacheInCloudFront[pre, post, response]
}

-- functions --
fun getMostRecentlyBuild[t: Time]: lone Build {
  (Build <: post).(max[Build.post & (prevs[t]+t)])
}

/*
* determine whether there is cached version of wanted 'Type' of asset in a 'StaticFileService' under given 'Time'
*/
fun inService[type: Type, store: StaticFileService, t: Time]: set Asset {
  store.assets[t] & uri.type
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

-- predications --
pred pushToS3[files: Asset, t,t': Time] {
  let oldFile = inService[files.uri, S3, t] {
    oldFile != none => S3.assets[t'] = S3.assets[t] - oldFile + files
    else
    S3.assets[t'] = S3.assets[t] + files
  }
}

pred cacheInCloudFront[pre,post: Time, files: set Asset] {
  let cache = inService[files.uri, Cloudfront, pre] {
    cache != none => Cloudfront.assets[post] = Cloudfront.assets[pre] -- cache found, do nothing
    else
    Cloudfront.assets[post] = Cloudfront.assets[pre] + files -- not found, set the cache
  }
}

-- facts --
fact noParallelBuilding {
  all disj b, b': Build|
    b.pre != b'.pre
}

fact versionIncreasing {
  all disj b, b': Build {
    lt[b.pre, b'.prev] => lt[b.v, b'.v] 
  }
}

fact {
  no StaticFileService.assets[Time/first] -- start with empty services
}

fact everyAssetBelongsToABuild {
  Asset = Build.dist
}

fact transitions {
  no Event.pre & Time/last
  and
  no Event.post & Time/first

  all t: Time - Time/last |
    let t' = t.next |
      some e: Event { 
        e.pre = t 
        e.post = t'
      }
  -- comment the following code to get concurrent situations
  all disj e,e': Event {
    no e.pre & e'.pre
  }

  all t: Time-last |
  let t' = t.next |
    one e: Event {
      e.pre = t and e.post = t'
      S3.assets[t'] != S3.assets[t] <=> e in Build
      Cloudfront.assets[t'] != Cloudfront.assets[t] => {
        e in Request
        Cloudfront.assets[t'] in e.response
      }
    }
}

fact S3ShouldBeTheSameWithoutAnyBuild {
  all t: Time - Time/first |
    no Build.post & t => S3.assets[t.prev] = S3.assets[t]
}

fact CloudfrontBeTheSameWithoutAnyRequest {
  all t: Time - Time/first |
    no Request.post & t => Cloudfront.assets[t.prev] = Cloudfront.assets[t]
}

/*
* test run, to see if I did anything wrong
*/
run {
  some Build
  and
  some Request
  and
  some response
} for 3 but exactly 3 Event,exactly 4 Asset, 4 Time -- examples would be found

/*
* check 1: counting
*
* No counter examples
*/
check {
  #Asset = mul[#Build, 2]
  all t: Time|
    let filesInS3 = S3.assets[t] {
      #filesInS3 = 0 or #filesInS3 = 2
      let t = filesInS3.uri | #t = 0 or #t = 2
    }
} for 12

/*
* check 2: for every 'Request' event, its assets' versions are the same
* and each 'Request' always receive the newest version of assets.
*
* This will find counter examples showing outdated 'Other' assets being returned
*/
check {
  all r: Request|
    all disj a: r.response |
      let recentBuild = getMostRecentlyBuild[r.pre] |
        some recentBuild => a.v = recentBuild.v
} for 3 but exactly 4 Event,exactly 4 Asset, exactly 5 Time
