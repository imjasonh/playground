# Positive cases: no want markers.

resource "aws_iam_role" "pinned" {
  name = "github-deploy"

  assume_role_policy = jsonencode({
    Version = "2012-10-17"
    Statement = [{
      Effect    = "Allow"
      Action    = "sts:AssumeRoleWithWebIdentity"
      Principal = { Federated = aws_iam_openid_connect_provider.github.arn }
      Condition = {
        StringEquals = {
          "token.actions.githubusercontent.com:aud" = "sts.amazonaws.com"
          "token.actions.githubusercontent.com:sub" = "repo:octo-org/octo-repo:environment:production"
        }
      }
    }]
  })
}

data "aws_iam_policy_document" "org_branches" {
  statement {
    actions = ["sts:AssumeRoleWithWebIdentity"]

    principals {
      type        = "Federated"
      identifiers = [aws_iam_openid_connect_provider.github.arn]
    }

    condition {
      test     = "StringEquals"
      variable = "token.actions.githubusercontent.com:aud"
      values   = ["sts.amazonaws.com"]
    }

    condition {
      test     = "StringLike"
      variable = "token.actions.githubusercontent.com:sub"
      values   = ["repo:octo-org/*:ref:refs/heads/main"]
    }
  }
}

resource "aws_iam_role" "from_document" {
  name               = "github-from-document"
  assume_role_policy = data.aws_iam_policy_document.org_branches.json
}

resource "aws_iam_role" "admin" {
  name = "admin"

  assume_role_policy = jsonencode({
    Version = "2012-10-17"
    Statement = [{
      Effect    = "Allow"
      Action    = "sts:AssumeRole"
      Principal = { AWS = "arn:aws:iam::123456789012:root" }
    }]
  })
}
