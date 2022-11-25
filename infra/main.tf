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
  instance_type = "t4g.nano"

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

#
# Elastic IP
#
resource "aws_eip" "lb" {
  instance = aws_instance.blog.id
  vpc      = true
}

output "lb_pulic_ip" {
  description = "Public IP address of the EC2 instance"
  value       = aws_eip.lb.public_ip
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
    aws_eip.lb.public_ip
  ]
}

resource "aws_route53_record" "txt" {
  zone_id = aws_route53_zone.zone.zone_id
  name    = "sadraskol.com"
  type    = "TXT"
  ttl     = "300"
  records = [
    "google-site-verification=zRcg7ny_ovzu8LbHhnepZuD_geb6_4TKmT6dpTxrYeQ",
    "keybase-site-verification=VjoXVCDQAZRhDYShuqrzDgj0IQoF4V0sRMzZwc9nA34",
    "protonmail-verification=577c04355c422286497bca6d5bbefede3b812708",
    "v=spf1 include:_spf.protonmail.ch mx ~all"
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
    aws_eip.lb.public_ip
  ]
}

resource "aws_route53_record" "proton" {
  for_each = {
    protonmail : "protonmail.domainkey.dknhsmf2w5ng3cpl6lqwf2agdgfkaqyl3oeeeoppk4muniovoyhla.domains.proton.ch.",
    protonmail2 : "protonmail2.domainkey.dknhsmf2w5ng3cpl6lqwf2agdgfkaqyl3oeeeoppk4muniovoyhla.domains.proton.ch.",
    protonmail3 : "protonmail3.domainkey.dknhsmf2w5ng3cpl6lqwf2agdgfkaqyl3oeeeoppk4muniovoyhla.domains.proton.ch."
  }

  zone_id = aws_route53_zone.zone.zone_id
  name    = "${each.key}.sadraskol.com"
  type    = "CNAME"
  ttl     = "3600"
  records = [each.value]
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

resource "aws_route53_record" "mx" {
  zone_id = aws_route53_zone.zone.zone_id
  name    = "sadraskol.com"
  type    = "MX"
  ttl     = "3600"
  records = [
    "10 mail.protonmail.ch",
    "20 mailsec.protonmail.ch"
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

#
# S3 for deployment
#
resource "aws_s3_bucket" "deploy_bucket" {
  bucket = "deploy.sadraskol.com"

  tags = {
    Name = "sadraskol deploy"
  }
}

resource "aws_s3_bucket_acl" "acl" {
  bucket = aws_s3_bucket.deploy_bucket.id
  acl    = "private"
}

resource "aws_s3_object" "dist" {
  bucket = aws_s3_bucket.deploy_bucket.id
  key    = "dist.tar.gz"
  acl    = "public-read"
}

#
# OpenID Connect provider
#
resource "aws_iam_openid_connect_provider" "default" {
  url = "https://token.actions.githubusercontent.com"

  client_id_list = ["gh-deploy"]

  thumbprint_list = ["6938fd4d98bab03faadb97b34396831e3780aea1"]
}

# Inspired by https://gist.github.com/guitarrapc/fc64be2fcfafc9bc13bb1e022bb0edf4
data "aws_iam_policy_document" "github_oid_assume_role_policy" {
  statement {
    effect  = "Allow"
    actions = ["sts:AssumeRoleWithWebIdentity"]
    principals {
      type        = "Federated"
      identifiers = [aws_iam_openid_connect_provider.default.arn]
    }
    condition {
      test     = "StringLike"
      variable = "token.actions.githubusercontent.com:aud"
      values   = ["gh-deploy"]
    }
    condition {
      test     = "StringLike"
      variable = "token.actions.githubusercontent.com:sub"
      values   = ["repo:sadraskol/sadraskol-blog:*"]
    }
  }
}

resource "aws_iam_role" "deploy_role" {
  name = "deploy_role"

  assume_role_policy = data.aws_iam_policy_document.github_oid_assume_role_policy.json
}

resource "aws_iam_policy" "policy" {
  name        = "deploy-policy"
  description = "Deploy policy"

  policy = jsonencode({
    Version = "2012-10-17"
    Statement = [
      {
        Action = ["s3:PutObject", "s3:PutObjectAcl"]
        Effect = "Allow"
        Resource = [
          "${aws_s3_bucket.deploy_bucket.arn}/*"
        ]
      },
    ]
  })
}

resource "aws_iam_role_policy_attachment" "deploy-attach" {
  role       = aws_iam_role.deploy_role.name
  policy_arn = aws_iam_policy.policy.arn
}

output "deploy_iam_arn" {
  description = "IAM deploy role arn"
  value       = aws_iam_role.deploy_role.arn
}
