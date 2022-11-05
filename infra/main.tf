terraform {
  required_providers {
    aws = {
      source  = "hashicorp/aws"
      version = "~> 4.16"
    }
  }
}

provider "aws" {
  region = "eu-west-3"
}

#
# KEY PAIR
#
resource "aws_key_pair" "deployer" {
  key_name   = "lenovo"
  public_key = "ssh-rsa AAAAB3NzaC1yc2EAAAADAQABAAABAQCaZodWDzevJd2iwbRwURODC3/WEIjCQ1hv+Q81xVj0JLN4B4ZAdM+6L1eeR6rqpKK48AZbi3ExdF3l663QUxC4BJjQJhUQQVrT/UNnexR2vpsDYSCkozeyvyiBk0ppX//bxbtQStRcsgEHBP0mRYIuVL9NvBkFXePIUE+HCkz0UpMP5jt4hroqRMborXFjytdjnNmS8wCSM6/dunoiWKlE9eEDgwMmkSejBSTPLyhIhcdIZfU1vpH+XDC+NDuRonYbJ4vjdO/IxabVCcWu/1bjHvuA2Ihdp8eKxGhmJRbDz87txx8yZ5eIhvyWEXqmYFS6xHOjNvM9y9Gcji2crT/7 lenovo"
}

#
# VPC
#
resource "aws_default_vpc" "default" {

}

resource "aws_security_group" "blog_security" {
  name        = "blog_security"
  description = "allow ssh on 22, http on port 80 & https on port 443"
  vpc_id      = aws_default_vpc.default.id

  ingress {
    from_port   = 22
    to_port     = 22
    protocol    = "tcp"
    cidr_blocks = ["0.0.0.0/0"]
  }

  ingress {
    from_port        = 443
    to_port          = 443
    protocol         = "tcp"
    cidr_blocks      = ["0.0.0.0/0"]
    ipv6_cidr_blocks = ["::/0"]

  }

  ingress {
    from_port        = 80
    to_port          = 80
    protocol         = "tcp"
    cidr_blocks      = ["0.0.0.0/0"]
    ipv6_cidr_blocks = ["::/0"]
  }

  egress {
    from_port   = 0
    to_port     = 0
    protocol    = "-1"
    cidr_blocks = ["0.0.0.0/0"]
  }
}

#
# AWS EC2 INSTANCE
#
resource "aws_instance" "blog" {
  ami           = "ami-02ea0a967c57de2d3"
  instance_type = "t4g.micro"

  key_name = aws_key_pair.deployer.key_name

  tags = {
    Name = "BlogServer"
  }

  security_groups = [
    aws_security_group.blog_security.name
  ]

  user_data                   = file("install.sh")
  user_data_replace_on_change = true
}

output "public_ip" {
  description = "Public IP address of the EC2 instance"
  value       = aws_instance.blog.public_ip
}

#
# ROUTE 53 IP ADRESSES
#
resource "aws_route53_zone" "zone" {
  name = "sadraskol.com"
}

resource "aws_route53_record" "a" {
  zone_id = aws_route53_zone.zone.zone_id
  name    = "sadraskol.com"
  type    = "A"
  ttl     = "300"
  records = [
    aws_instance.blog.public_ip
  ]
}

resource "aws_route53_record" "txt" {
  zone_id = aws_route53_zone.zone.zone_id
  name    = "sadraskol.com"
  type    = "TXT"
  ttl     = "300"
  records = [
    "google-site-verification=zRcg7ny_ovzu8LbHhnepZuD_geb6_4TKmT6dpTxrYeQ",
    "keybase-site-verification=VjoXVCDQAZRhDYShuqrzDgj0IQoF4V0sRMzZwc9nA34"
  ]
}

resource "aws_route53_record" "bing" {
  zone_id = aws_route53_zone.zone.zone_id
  name    = "b68bf3d270066c00c9fd509050ef73fe.sadraskol.com"
  type    = "CNAME"
  ttl     = "300"
  records = ["verify.bing.com"]
}

resource "aws_route53_record" "www" {
  zone_id = aws_route53_zone.zone.zone_id
  name    = "www.sadraskol.com"
  type    = "A"
  ttl     = "300"
  records = [
    aws_instance.blog.public_ip
  ]
}

resource "aws_route53_record" "ns" {
  zone_id = aws_route53_zone.zone.zone_id
  name    = "sadraskol.com"
  type    = "NS"
  ttl     = "172800"
  records = [
    "ns-389.awsdns-48.com.",
    "ns-754.awsdns-30.net.",
    "ns-1575.awsdns-04.co.uk.",
    "ns-1495.awsdns-58.org."
  ]
}

resource "aws_route53_record" "soa" {
  zone_id = aws_route53_zone.zone.zone_id
  name    = "sadraskol.com"
  type    = "SOA"
  ttl     = "900"
  records = [
    "ns-389.awsdns-48.com. awsdns-hostmaster.amazon.com. 1 7200 900 1209600 86400"
  ]
}
