resource "aws_s3_bucket" "public" { # want "S3 ACL grants public"
  bucket = "example-public"
  acl    = "public-read"
}

resource "aws_s3_bucket_acl" "public" { # want "S3 ACL grants public"
  bucket = "example-public"
  acl    = "public-read-write"
}

resource "aws_s3_bucket_public_access_block" "open" { # want "public access block has a protection set to false"
  bucket              = "example-public"
  block_public_acls   = false
  block_public_policy = true
}
