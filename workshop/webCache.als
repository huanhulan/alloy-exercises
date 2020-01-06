open util/time
open util/ordering[BuildVersion]

sig BuildVersion{}

abstract sig StaticFileService {
  assets: set Asset
}

one sig S3 extends StaticFileService{}
one sig Cloudfront extends StaticFileService{}

abstract sig Asset{
  uri: Type,
  etag: BuildVersion,
}

abstract sig Type {}
sig Entry extends Type{}
sig Other extends Type{}