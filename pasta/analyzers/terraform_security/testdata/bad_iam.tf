resource "aws_iam_policy" "admin" { # want "Action * on Resource *"
  policy = jsonencode({
    Statement = [{
      Action   = "*"
      Resource = "*"
    }]
  })
}

resource "aws_iam_role_policy" "admin" { # want "Action * on Resource *"
  role = "example"
  policy = <<EOF
{
  "Statement": [{
    "Action": "*",
    "Resource": "*"
  }]
}
EOF
}
