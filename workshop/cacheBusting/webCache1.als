/*
* Cache busting with build hash
*/
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

one sig Server {
  hash: Time -> lone BuildVersion,
  uris: Time -> set Type
} {
  hash[Time/first] = none

  uris[Time/first] = none
  all t: Time - Time/first | uris[t] = Entry + Other
}

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
  
  updateServer[v, post]
  pushToS3[dist, post]
}

/*
* 'Request' Event: issue 2 'request's, one for entry, the other for 'Other' without param.
* And if some fetched resources can't be found in current 'S3', then put resources into the 'next' state of 'S3'.
* Storing the returning assets into event's 'response' filed.
*/
sig Request extends Event {
  response: set Asset
}{
  /*
  * For this version, the url of static assets in HTML file returned by the server would always contains
  * a same build hash comes from last build, like 'index.a1b2cdefg.js'
  */ 
  let v = Server.hash[pre] |
    let uris = Server.uris[pre] {
    uris != none => {
      response = request[Entry, v, pre, none] + request[Other, v, pre, none]
      cacheToCloudFront[post, response]
    } else 
    response = none
  }
}

-- functions --
fun getMostRecentlyBuild[t: Time]: lone Build {
  (Build <: post).(max[Build.post & (prevs[t]+t)])
}

/*
* Now that our filename are composed of 'Type' and 'BuildVersion', so need to 
* determine whether there is any assets matched with given conditions in a 'StaticFileService' under given 'Time'
*/
fun inService[type: Type, hash: BuildVersion, store: StaticFileService, t: Time]: set Asset {
  store.assets[t] & uri.type & v.hash
}

/*
* request: if 'urlParam' is represented, filter corresponding resource from 'Cloudfront',
* otherwise from 'S3',
* if fetching from 'Cloudfront', always return the 'max' version of the type.
*/
fun request[type: Type, v: BuildVersion, t: Time, urlParam: Int]: set Asset {
  let f = inService[type, v, Cloudfront, t] |
    let f' = inService[type, v, S3, t] {
      urlParam != none => f' else {
        f != none => f
        else
        f'
      }
    }
}

-- predications --
pred pushToS3[files: Asset, t': Time] {
  let t = prev[t'] |
    let oldFile = inService[files.uri, files.v, S3, t] {
      oldFile != none => S3.assets[t'] = S3.assets[t] - oldFile + files
      else
      S3.assets[t'] = S3.assets[t] + files
    }
}

pred updateServer[v: BuildVersion, t: Time] {
  Server.hash[t] = v
}

pred cacheToCloudFront[post: Time, files: set Asset] {
  let pre = prev[post] |
    -- To avoid higher-order logic, supposing all the files share the same build hash
    let cache = inService[files.uri, files.v, Cloudfront, pre] {
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

fact startWithEmpty {
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
      (
        S3.assets[t'] != S3.assets[t]
        and
        Server.hash[t'] != Server.hash[t]
      ) <=> e in Build
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

-- reducing the amount of subexpressions to speed up solving
fact {
  #Asset = mul[#BuildVersion, 2]
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
} for 3 but exactly 12 Event, 22 Asset, 11 BuildVersion, exactly 13 Time -- examples would be found

/*
* check: for every 'Request' event, its assets' versions are the same
* and each 'Request' always receive the newest version of assets.
* Due to 'Scope Monotonicity', we don't need to check the scope setting for
* the old version
*/
check {
  all r: Request|
    all disj a: r.response |
      let recentBuild = getMostRecentlyBuild[r.pre] |
        some recentBuild => a.v = recentBuild.v
} for 3 but exactly 10 Event, 18 Asset, 9 BuildVersion, exactly 11 Time -- no counter examples, took about 10 hours to solve
