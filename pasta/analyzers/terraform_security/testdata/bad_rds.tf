resource "aws_db_instance" "public" { # want "publicly accessible" # want "not encrypted" # want "password is a string literal"
  instance_class      = "db.t3.micro"
  publicly_accessible = true
  password            = "hunter2"
}

resource "aws_rds_cluster" "plain" { # want "not encrypted"
  engine = "aurora-mysql"
}
