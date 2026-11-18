resource "aws_iam_role" "aud_only" { # want "so any GitHub repository can assume it"
  name = "github-aud-only"

  assume_role_policy = jsonencode({
    Version = "2012-10-17"
    Statement = [{
      Effect    = "Allow"
      Action    = "sts:AssumeRoleWithWebIdentity"
      Principal = { Federated = aws_iam_openid_connect_provider.github.arn }
      Condition = {
        StringEquals = {
          "token.actions.githubusercontent.com:aud" = "sts.amazonaws.com"
        }
      }
    }]
  })
}

data "aws_iam_policy_document" "no_condition" { # want "so any GitHub repository can assume it"
  statement {
    actions = ["sts:AssumeRoleWithWebIdentity"]

    principals {
      type        = "Federated"
      identifiers = ["arn:aws:iam::123456789012:oidc-provider/token.actions.githubusercontent.com"]
    }
  }
}

resource "aws_iam_role" "any_repo" { # want "wildcard in the owner"
  name = "github-any-repo"

  assume_role_policy = <<EOF
{
  "Version": "2012-10-17",
  "Statement": [{
    "Effect": "Allow",
    "Action": "sts:AssumeRoleWithWebIdentity",
    "Principal": {"Federated": "arn:aws:iam::123456789012:oidc-provider/token.actions.githubusercontent.com"},
    "Condition": {
      "StringLike": {"token.actions.githubusercontent.com:sub": "repo:*"}
    }
  }]
}
EOF
}

resource "aws_iam_role" "star_sub" { # want "wildcard in the owner"
  name = "github-star"

  assume_role_policy = jsonencode({
    Version = "2012-10-17"
    Statement = [{
      Effect    = "Allow"
      Action    = "sts:AssumeRoleWithWebIdentity"
      Principal = { Federated = aws_iam_openid_connect_provider.github.arn }
      Condition = {
        StringLike = {
          "token.actions.githubusercontent.com:sub" = "*"
        }
      }
    }]
  })
}

data "aws_iam_policy_document" "star_values" { # want "wildcard in the owner"
  statement {
    actions = ["sts:AssumeRoleWithWebIdentity"]

    principals {
      type        = "Federated"
      identifiers = [aws_iam_openid_connect_provider.github.arn]
    }

    condition {
      test     = "StringLike"
      variable = "token.actions.githubusercontent.com:sub"
      values   = ["*"]
    }
  }
}

data "aws_iam_policy_document" "owner_prefix" { # want "wildcard in the owner"
  statement {
    actions = ["sts:AssumeRoleWithWebIdentity"]

    principals {
      type        = "Federated"
      identifiers = [aws_iam_openid_connect_provider.github.arn]
    }

    condition {
      test     = "StringLike"
      variable = "token.actions.githubusercontent.com:sub"
      values   = ["repo:octo-org*/deploy:*"]
    }
  }
}
