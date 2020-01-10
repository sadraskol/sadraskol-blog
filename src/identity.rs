use actix_identity::{CookieIdentityPolicy, IdentityService, RequestIdentity};
use actix_web::{Error, http, HttpResponse};
use actix_web::dev::{Service, ServiceRequest, ServiceResponse, Transform};
use futures::future::{Either, ok, Ready};
use futures::task::{Context, Poll};

use crate::config::Config;

pub fn identity_service(config: Config) -> IdentityService<CookieIdentityPolicy> {
    if cfg!(features = "production") {
        IdentityService::new(
            CookieIdentityPolicy::new(config.cookie_seed.as_bytes())
                .name("sadraskol")
                .secure(true),
        )
    } else {
        IdentityService::new(
            CookieIdentityPolicy::new(config.cookie_seed.as_bytes())
                .name("sadraskol")
                .secure(false),
        )
    }
}

pub struct CheckAdmin;

impl<S, B> Transform<S> for CheckAdmin
    where
        S: Service<Request=ServiceRequest, Response=ServiceResponse<B>, Error=Error>,
        S::Future: 'static,
{
    type Request = ServiceRequest;
    type Response = ServiceResponse<B>;
    type Error = Error;
    type Transform = CheckAdminMiddleware<S>;
    type InitError = ();
    type Future = Ready<Result<Self::Transform, Self::InitError>>;

    fn new_transform(&self, service: S) -> Self::Future {
        ok(CheckAdminMiddleware { service })
    }
}

pub struct CheckAdminMiddleware<S> {
    service: S,
}

impl<S, B> Service for CheckAdminMiddleware<S>
    where
        S: Service<Request=ServiceRequest, Response=ServiceResponse<B>, Error=Error>,
        S::Future: 'static,
{
    type Request = ServiceRequest;
    type Response = ServiceResponse<B>;
    type Error = Error;
    type Future = Either<S::Future, Ready<Result<Self::Response, Self::Error>>>;

    fn poll_ready(&mut self, cx: &mut Context) -> Poll<Result<(), Self::Error>> {
        self.service.poll_ready(cx)
    }

    fn call(&mut self, req: ServiceRequest) -> Self::Future {
        // We only need to hook into the `start` for this middleware.

        let is_logged_in = req.get_identity()
            .map(|d| d == "admin")
            .unwrap_or(false);

        if is_logged_in {
            Either::Left(self.service.call(req))
        } else {
            // Don't forward to /login if we are already on /login
            if req.path() == "/login" {
                Either::Left(self.service.call(req))
            } else {
                Either::Right(ok(req.into_response(
                    HttpResponse::Found()
                        .header(http::header::LOCATION, "/login")
                        .finish()
                        .into_body(),
                )))
            }
        }
    }
}