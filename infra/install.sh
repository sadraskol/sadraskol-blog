#!/usr/bin/bash
set -e

# install everything we need
sudo apt update -y
sudo apt install -y nginx certbot python3-certbot-nginx

sudo -u ubuntu mkdir /home/ubuntu/blog

echo "<!doctype html>
<html lang=\"en\">
<head>
    <title>{{ title }}</title>
    <meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">
    <link rel=\"alternate\" type=\"application/rss+xml\" title=\"Sadraskol\'s blog\" href=\"https://sadraskol.com/feed\">
    <style>
        fieldset {
            border: 0;
            padding: 0;
            margin: 0;
        }

        a {
            color: hsl(345.52, 100.0%, 77.25%);
            text-decoration: none
        }

        a:hover {
            text-decoration: underline;
            cursor: pointer
        }

        img {
            max-width: 100%;
        }

        body {
            margin: 0 0 0 0;
            font-family: \"Helvetica Neue\", \"Helvetica\", \"Arial\", sans-serif;
            background-color: hsl(22.11, 65.52%, 94.31%);
            color: hsl(344.0, 9.2%, 31.96%)
        }

        strong {
            color: hsl(345.0, 13.33%, 17.65%)
        }

        header {
            display: flex;
            flex-direction: row;
            justify-content: space-between;
            color: hsl(345.0, 13.33%, 17.65%)
        }

        header nav {
            padding-top: 1.0em;
            padding-bottom: 1.0em
        }

        .container {
            max-width: 700px;
            margin: 0 auto 0 auto;
            padding: 0 1em 0 1em;
        }

        figure img {
            display: block;
            margin: 0 auto 0.5em auto;
        }

        figure figcaption {
            text-align: center;
        }

        code {
            background-color: #fffffe;
        }

        pre code {
            background-color: #fffffe;
            overflow-x: auto;
            padding: 0.5em 0.5em 0.5em 0.5em;
            display: block;
        }

        blockquote {
            margin: 0 0 0 0;
            padding: 0.5em 1.5em 0.5em 3em;
            position: relative;
        }

        blockquote::before {
            content: \"\201C\";
            color: hsl(345.52, 100.0%, 77.25%);
            position: absolute;
            left: 0;
            font-size: 100px;
            line-height: 1;
        }

        .post-item {
            margin: 1.0em 0 0 0
        }

        .post-item:last-child {
            margin-bottom: 1.0em
        }

        .post-item__actions {
            display: flex;
            flex-direction: row;
            margin: 0 0 0 0;
            padding: 3.0px 0 0 0;
            list-style-type: none
        }

        .post-item__actions__item {
            position: relative;
            display: block;
            padding: 0 30.0px 0 0
        }

        .index-item {
            display: flex;
            margin: 1.0em 0 0 0;
        }
        .index-item:last-child {
            margin-bottom: 1.0em
        }
        .index-item_datetime {
            position: relative;
            display: block;
            padding: 0 30.0px 0 0;
            flex-basis: 8em;
            flex-shrink: 0;
        }

        .post-item__actions__item form button {
            background: none !important;
            border: none;
            padding: 0 !important;
            text-decoration: none;
            font: inherit;
            color: hsl(345.52, 100.0%, 77.25%);
        }

        .post-item__actions__item form button:hover {
            text-decoration: underline;
            cursor: pointer
        }

        #editor-content__textarea {
            width: 100%;
            height: 400px;
            padding: 1em;
            margin-bottom: 1em;
            display: block;
            resize: vertical;
        }

        .back-link {
            display: block;
            margin-bottom: 1em;
        }

        table th {
          text-align: center;
          padding: 8px 8px;
        }
        
        table td {
          text-align: center;
          padding: 8px 8px;
        }
        
        table tr {
          border-bottom: solid 1px #aaa;
        }

        table {
          border-collapse: collapse;
        }

        /* Github gist style from highlight js */
        .h-comment,
        .h-meta {
            color: #969896
        }

        .h-variable,
        .h-template-variable,
        .h-strong,
        .h-emphasis,
        .h-quote {
            color: #df5000
        }

        .h-keyword,
        .h-selector-tag,
        .h-type {
            color: #d73a49
        }

        .h-literal,
        .h-symbol,
        .h-bullet,
        .h-attribute {
            color: #0086b3
        }

        .h-section,
        .h-name {
            color: #63a35c
        }

        .h-tag {
            color: #333333
        }

        .h-title,
        .h-attr,
        .h-selector-id,
        .h-selector-class,
        .h-selector-attr,
        .h-selector-pseudo {
            color: #6f42c1
        }

        .h-addition {
            color: #55a532;
            background-color: #eaffea
        }

        .h-deletion {
            color: #bd2c00;
            background-color: #ffecec
        }

        .h-number {
            color: #005cc5;
            font-weight: bold
        }

        .h-string {
            color: #032f62
        }
    </style>
</head>
<body>
<div>
    <header class=\"container\">
        <h1><a href="/">Sadraskol</a></h1>
    </header>
    <div class=\"container\">
        <p>Maintenance mode!</p>
    </div>
</div>
</body>
</html>
" | sudo -u ubuntu tee /home/ubuntu/blog/index.html

echo "server {
    root /home/ubuntu/blog;
    index index.html;
    server_name sadraskol.com www.sadraskol.com;
}
" | sudo tee /etc/nginx/sites-available/default

echo "user www-data;
worker_processes auto;
pid /run/nginx.pid;
include /etc/nginx/modules-enabled/*.conf;

events {
    worker_connections 768;
}

http {
    sendfile on;
    tcp_nopush on;
    tcp_nodelay on;
    keepalive_timeout 65;
    types_hash_max_size 2048;

    charset utf-8;

    include /etc/nginx/mime.types;
    default_type application/octet-stream;

    ssl_protocols TLSv1 TLSv1.1 TLSv1.2;
    ssl_prefer_server_ciphers on;

    access_log /var/log/nginx/access.log;
    error_log /var/log/nginx/error.log;

    gzip on;

    include /etc/nginx/conf.d/*.conf;
    include /etc/nginx/sites-enabled/*;
}
" | sudo tee /etc/nginx/nginx.conf

sudo gpasswd -a www-data ubuntu
sudo systemctl restart nginx

sudo certbot --nginx -d sadraskol.com -d www.sadraskol.com -n -m thchblog@gmail.com --agree-tos

echo "[Unit]
Description=Renew Certbot certificates
Wants=certbot-renew.timer
Require=nginx.service

[Service]
Type=oneshot
WorkingDirectory=/etc/letsencrypt
ExecStart=/usr/bin/certbot renew -n
ExecStart=/usr/bin/systemctl restart nginx

[Install]
WantedBy=multi-user.target" | sudo tee /etc/systemd/system/certbot-renew.service

echo "[Unit]
Description=Daily Certbot renew

[Timer]
OnCalendar=daily
Persistent=true

[Install]
WantedBy=timers.target" | sudo tee /etc/systemd/system/certbot-renew.timer

echo '#!/usr/bin/bash
set -e
remote=$(curl -I https://s3.eu-west-3.amazonaws.com/deploy.sadraskol.com/dist.tar.gz | grep ETag)
touch dist.etag
if [[ "$remote" != "$(cat dist.etag)" ]]; then
    echo $remote > dist.etag
    curl https://s3.eu-west-3.amazonaws.com/deploy.sadraskol.com/dist.tar.gz --output dist.tar.gz
    tar xfz dist.tar.gz
    rm -rf blog
    mv dist blog
    rm dist.tar.gz
fi
' | sudo -u ubuntu tee /home/ubuntu/update-sadraskol.sh

sudo chmod +x /home/ubuntu/update-sadraskol.sh

echo "[Unit]
Description=Sadraskol Deploy Check
Wants=sadraskol.timer

[Service]
User=ubuntu
Type=oneshot
WorkingDirectory=/home/ubuntu
ExecStart=/home/ubuntu/update-sadraskol.sh

[Install]
WantedBy=multi-user.target" | sudo tee /etc/systemd/system/sadraskol.service

echo "[Unit]
Description=Minutely Sadraskol Check

[Timer]
OnCalendar=minutely
Persistent=true

[Install]
WantedBy=timers.target" | sudo tee /etc/systemd/system/sadraskol.timer

sudo systemctl daemon-reload
sudo systemctl start certbot-renew.service
sudo systemctl start certbot-renew.timer
sudo systemctl start sadraskol.service
sudo systemctl start sadraskol.timer

