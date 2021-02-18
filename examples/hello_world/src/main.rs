#[macro_use] extern crate rocket;

use std::{char, str::FromStr};

use rocket::{Request, Responder, Response, http::{Header, Status, hyper::HeaderName}, request::FromRequest};
use rocket::request::{Outcome};

#[cfg(test)] mod tests;

#[derive(Responder)]
struct MyResponse {
    text: &'static str,
    header: Header<'static>
}

 struct MyHeader(String);

#[derive(Debug)]
    struct MyHeaderError {
}
/*
const fn check(header_name: &str) -> bool {
    let header_name = header_name.as_bytes();
    let n = header_name.len();
    let mut i = 0;
    let mut safe = true;
    while i < n {
        if header_name[i] > 127 {
            return false;
        }
        i += 1;
    }
    true
}

const fn check_header(header_name: &str) {
    let safe = check(header_name);
    let _ = [(); 0 - (!(safe) as usize)];
}

macro_rules! header_name {
    ($name:tt) => { {
            check_header($name);
            HeaderName::from_str($name).unwrap()
        }
    }
}

fn dope() -> HeaderName {
    header_name!("hej")
}
*/
#[rocket::async_trait]
impl<'a, 'r> FromRequest<'a, 'r> for MyHeader {
    type Error = MyHeaderError;

    async fn from_request(req: &'a Request<'r>) -> Outcome<Self, Self::Error> {
        let keys: Vec<_> = req.headers().get("MyHeader").collect();
        match keys.len() {
            1 => Outcome::Success(MyHeader(keys[0].to_str().unwrap().to_owned())),
            _ => Outcome::Failure((Status::BadRequest, MyHeaderError {})),
        }
    }
}

#[get("/?<name>")]
fn hello(my_header: Option<MyHeader>, name: String) -> MyResponse {
    //let some_header = dope();
    let val = if my_header.is_some() {
        my_header.unwrap().0 + &name
    } else {
        "default".into()
    };
    MyResponse {
        text: "Hello, world!",
        header: Header::new("Custom", val)
    }
}

#[launch]
fn rocket() -> rocket::Rocket {
    rocket::ignite().mount("/", routes![hello])
}
