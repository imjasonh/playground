resource "aws_instance" "open" { # want "not forced to IMDSv2" # want "associates a public IP"
  ami                         = "ami-12345678"
  instance_type               = "t3.micro"
  associate_public_ip_address = true

  ebs_block_device { # want "EBS block device has encrypted = false"
    device_name = "/dev/sdh"
    encrypted   = false
  }

  root_block_device { # want "root block device has encrypted = false"
    encrypted = false
  }
}

resource "aws_ebs_volume" "plain" { # want "EBS volume is not encrypted"
  availability_zone = "us-west-2a"
  size              = 10
}

resource "aws_launch_template" "v1" { # want "not forced to IMDSv2"
  image_id = "ami-12345678"
}
