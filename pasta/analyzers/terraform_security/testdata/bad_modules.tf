module "registry" { # want "not pinned to a full git commit SHA"
  source  = "hashicorp/consul/aws"
  version = "0.1.0"
}

module "git_tag" { # want "not pinned to a full git commit SHA"
  source = "git::https://github.com/terraform-aws-modules/terraform-aws-vpc.git?ref=v5.0.0"
}

module "insecure_git" { # want "unencrypted git://"
  source = "git://github.com/example/mod.git?ref=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
}
