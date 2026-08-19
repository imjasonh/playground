resource "aws_security_group" "ssh" {
  ingress { # want "allows SSH (22) from 0.0.0.0/0"
    from_port   = 22
    to_port     = 22
    protocol    = "tcp"
    cidr_blocks = ["0.0.0.0/0"]
  }
}

resource "aws_security_group" "rdp" {
  ingress { # want "allows RDP (3389) from 0.0.0.0/0"
    cidr_blocks = ["0.0.0.0/0"]
    from_port   = 3389
    to_port     = 3389
    protocol    = "tcp"
  }
}

resource "aws_security_group" "all" {
  ingress { # want "allows all traffic from 0.0.0.0/0"
    from_port   = 0
    to_port     = 0
    protocol    = "-1"
    cidr_blocks = ["0.0.0.0/0"]
  }
}

resource "aws_security_group_rule" "ssh" { # want "security group rule allows SSH"
  type              = "ingress"
  from_port         = 22
  to_port           = 22
  protocol          = "tcp"
  cidr_blocks       = ["0.0.0.0/0"]
  security_group_id = "sg-123"
}
