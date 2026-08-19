resource "aws_lb_listener" "http" { # want "uses HTTP instead of HTTPS"
  protocol = "HTTP"
}

resource "aws_sns_topic" "plain" { # want "SNS topic is not encrypted"
  name = "alerts"
}

resource "aws_sqs_queue" "plain" { # want "SQS queue is not encrypted"
  name = "jobs"
}

resource "aws_eks_cluster" "public" { # want "API endpoint is publicly reachable"
  name = "public"
}
