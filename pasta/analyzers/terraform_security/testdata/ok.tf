# Positive cases: hardened resources. No want markers.

provider "aws" {
  region = "us-west-2"
}

module "vpc" {
  source = "git::https://github.com/terraform-aws-modules/terraform-aws-vpc.git?ref=a1b2c3d4e5f6a1b2c3d4e5f6a1b2c3d4e5f6a1b2"
}

module "local" {
  source = "./modules/network"
}

resource "aws_db_instance" "ok" {
  instance_class      = "db.t3.micro"
  storage_encrypted   = true
  publicly_accessible = false
  username            = "admin"
  password            = var.db_password
}

resource "aws_ebs_volume" "ok" {
  availability_zone = "us-west-2a"
  size              = 10
  encrypted         = true
}

resource "aws_s3_bucket" "ok" {
  bucket = "example-private"
}

resource "aws_s3_bucket_acl" "ok" {
  bucket = aws_s3_bucket.ok.id
  acl    = "private"
}

resource "aws_s3_bucket_public_access_block" "ok" {
  bucket                  = aws_s3_bucket.ok.id
  block_public_acls       = true
  block_public_policy     = true
  ignore_public_acls      = true
  restrict_public_buckets = true
}

resource "aws_security_group" "ok" {
  ingress {
    from_port   = 22
    to_port     = 22
    protocol    = "tcp"
    cidr_blocks = ["10.0.0.0/8"]
  }
}

resource "aws_instance" "ok" {
  ami                         = "ami-12345678"
  instance_type               = "t3.micro"
  associate_public_ip_address = false

  metadata_options {
    http_tokens = "required"
  }

  root_block_device {
    encrypted = true
  }
}

resource "aws_lb_listener" "ok" {
  protocol = "HTTPS"
}

resource "aws_sns_topic" "ok" {
  kms_master_key_id = "alias/aws/sns"
}

resource "aws_sqs_queue" "ok" {
  kms_master_key_id = "alias/aws/sqs"
}

resource "aws_iam_policy" "ok" {
  policy = jsonencode({
    Statement = [{
      Action   = ["s3:GetObject"]
      Resource = "arn:aws:s3:::example/*"
    }]
  })
}

resource "aws_eks_cluster" "ok" {
  name = "ok"

  vpc_config {
    endpoint_public_access = false
  }
}

resource "azurerm_storage_account" "ok" {
  https_traffic_only_enabled = true
}

resource "azurerm_network_security_rule" "ok" {
  access                   = "Allow"
  direction                = "Inbound"
  destination_port_range   = "22"
  source_address_prefix    = "10.0.0.0/8"
}

resource "google_compute_firewall" "ok" {
  source_ranges = ["10.0.0.0/8"]

  allow {
    protocol = "tcp"
    ports    = ["22"]
  }
}

resource "google_container_cluster" "ok" {
  enable_legacy_abac = false
}
