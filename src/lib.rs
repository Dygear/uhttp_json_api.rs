//! This crate provides some utilities for reading HTTP JSON requests.

#![feature(try_from)]

extern crate serde;
extern crate serde_json;
extern crate subslice_index;
extern crate uhttp_body_bytes;
extern crate uhttp_chunked_bytes;
extern crate uhttp_content_encoding;
extern crate uhttp_media_type;
extern crate uhttp_method;
extern crate uhttp_request;
extern crate uhttp_request_target;
extern crate uhttp_status;
extern crate uhttp_transfer_encoding;
extern crate uhttp_uri;
extern crate uhttp_version;

#[cfg(test)]
#[macro_use]
extern crate serde_derive;

use std::ascii::AsciiExt;
use std::convert::TryFrom;
use std::io::Read;

use serde::Deserialize;
use subslice_index::subslice_index;
use uhttp_body_bytes::BodyBytes;
use uhttp_chunked_bytes::ChunkedBytes;
use uhttp_content_encoding::{content_encodings, ContentEncoding, StdContentEncoding};
use uhttp_media_type::{MediaType, MediaParams};
use uhttp_method::Method;
use uhttp_request::{RequestLine, Header, Headers};
use uhttp_request_target::RequestTarget;
use uhttp_status::StatusCode;
use uhttp_transfer_encoding::{transfer_encodings, TransferEncoding, StdTransferEncoding};
use uhttp_uri::{HttpUri, HttpResource};
use uhttp_version::HttpVersion;

/// Result with an HTTP status code error.
pub type HttpResult<T> = std::result::Result<T, StatusCode>;

/// Format of a request body [RFC7230§3.3.3].
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum RequestBodyFormat {
    /// Body contains the specified number of bytes.
    Sized(usize),
    /// Body is in chunked encoding format.
    Chunked,
    /// Body ends when the connection is closed.
    Closed,
}

/// Handles headers related to determining the request body format.
struct RequestBodyHeaders {
    /// Current transfer encoding of the body.
    tenc: Option<StdTransferEncoding>,
    /// Current explicit length of the body.
    len: Option<usize>,
}

impl Default for RequestBodyHeaders {
    fn default() -> Self {
        RequestBodyHeaders {
            tenc: None,
            len: None,
        }
    }
}

impl RequestBodyHeaders {
    /// Update the current view of the request body using the given header.
    pub fn process_header(&mut self, hdr: &Header) -> HttpResult<()> {
        if hdr.name.eq_ignore_ascii_case("content-encoding") {
            let val = std::str::from_utf8(hdr.val).map_err(|_| StatusCode::BadRequest)?;

            for enc in content_encodings(val) {
                match enc {
                    ContentEncoding::Std(StdContentEncoding::Identity) => {},
                    _ => return Err(StatusCode::NotImplemented),
                }
            }
        } else if hdr.name.eq_ignore_ascii_case("content-length") {
            let next = std::str::from_utf8(hdr.val)
                .map_err(|_| StatusCode::BadRequest)?
                .trim().parse().map_err(|_| StatusCode::BadRequest)?;

            if let Some(len) = self.len {
                // Multiple given lengths must match [RFC7230§3.3.2].
                if len != next {
                    return Err(StatusCode::BadRequest);
                }
            } else {
                self.len = Some(next);
            }
        } else if hdr.name.eq_ignore_ascii_case("transfer-encoding") {
            use self::TransferEncoding::*;
            use self::StdTransferEncoding::*;

            let val = std::str::from_utf8(hdr.val).map_err(|_| StatusCode::BadRequest)?;

            for enc in transfer_encodings(val) {
                // Only support a single encoding layer.
                if self.tenc.is_some() {
                    return Err(StatusCode::NotImplemented);
                }

                if let Std(Chunked) = enc {
                    self.tenc = Some(Chunked);
                } else {
                    return Err(StatusCode::NotImplemented);
                }
            }
        } else if hdr.name.eq_ignore_ascii_case("content-type") {
            let val = std::str::from_utf8(hdr.val).map_err(|_| StatusCode::BadRequest)?;
            let media = MediaType::new(val).map_err(|_| StatusCode::BadRequest)?;

            if !media.mimetype.eq_ignore_ascii_case("application/json") {
                return Err(StatusCode::NotImplemented);
            }

            for param in MediaParams::new(media.params) {
                let (name, val) = param.map_err(|_| StatusCode::BadRequest)?;

                if !name.eq_ignore_ascii_case("charset") ||
                   !val.inner().eq_ignore_ascii_case("utf-8")
                {
                    return Err(StatusCode::NotImplemented);
                }
            }
        }

        Ok(())
    }

    /// Parse a request body format if the current state is valid.
    pub fn into_format(self) -> HttpResult<RequestBodyFormat> {
        match (self.tenc, self.len) {
            (Some(StdTransferEncoding::Chunked), None) =>
                Ok(RequestBodyFormat::Chunked),
            (None, Some(len)) => Ok(RequestBodyFormat::Sized(len)),
            (None, None) => Ok(RequestBodyFormat::Closed),
            // Both present is an error [RFC7230§3.3.3].
            (Some(_), Some(_)) => Err(StatusCode::BadRequest),
            (Some(_), None) => unreachable!(),
        }
    }
}

/// Handles request routing and JSON deserialization.
pub struct HttpRequest<'a, S: Read> {
    /// Underlying stream to read bytes from.
    stream: S,
    /// Buffer to read request header and body into.
    buf: &'a mut [u8],
    /// Number of valid bytes in `buf`.
    len: usize,
    /// Current byte position in `buf`.
    pos: usize,
}

impl<'a, S: Read> HttpRequest<'a, S> {
    /// Create a new `HttpRequest` over the given stream, backed by the given buffer.
    ///
    /// The buffer is [recommended](https://tools.ietf.org/html/rfc7230#section-3.1.1) to
    /// hold at least 8000 bytes.
    pub fn new(mut stream: S, buf: &'a mut [u8]) -> HttpResult<Self> {
        match stream.read(&mut buf[..]) {
            Ok(len) => Ok(HttpRequest {
                stream: stream,
                buf: buf,
                len: len,
                pos: 0,
            }),
            Err(_) => Err(StatusCode::InternalServerError),
        }
    }

    /// Try to extract a version, method, and route.
    pub fn route<'b, R>(&'b mut self) -> HttpResult<(HttpVersion, Method, R)>
        where R: TryFrom<HttpResource<'b>, Err=StatusCode>
    {
        let (reqline, rest) = RequestLine::new(&self.buf[..self.len])
            .map_err(|err| match err {
                uhttp_request::Error::Partial => StatusCode::UriTooLong,
                uhttp_request::Error::Syntax => StatusCode::BadRequest,
            })?;

        self.pos = subslice_index(&self.buf[..], rest);

        let method = reqline.method.parse::<Method>()
            .map_err(|_| StatusCode::BadRequest)?;

        let target = reqline.target.parse::<RequestTarget>()
            .map_err(|_| StatusCode::BadRequest)?;

        let ver = reqline.version.parse::<HttpVersion>()
            .map_err(|_| StatusCode::BadRequest)?;

        let url = match target {
            RequestTarget::AbsPath =>
                HttpResource::new(reqline.target),
            RequestTarget::AbsUri =>
                // TODO: verify authority
                HttpUri::new(reqline.target)
                    .map_err(|_| StatusCode::BadRequest)?.resource,
            _ => return Err(StatusCode::NotImplemented),
        };

        let route = R::try_from(url)?;

        Ok((ver, method, route))
    }

    /// Try to deserialize a JSON payload from the request body.
    pub fn read_json<D: Deserialize>(&mut self) -> HttpResult<D> {
        let fmt = self.process_headers()?;
        let bytes = BodyBytes::new(&mut self.stream, &mut self.buf[..],
                                   self.pos, self.len);

        let msg = match fmt {
            RequestBodyFormat::Closed =>
                serde_json::from_iter(bytes),
            RequestBodyFormat::Sized(b) =>
                serde_json::from_iter(bytes.take(b)),
            RequestBodyFormat::Chunked =>
                serde_json::from_iter(ChunkedBytes::new(bytes)),
        };

        msg.map_err(|_| StatusCode::BadRequest)
    }

    /// Process the request headers.
    fn process_headers(&mut self) -> HttpResult<RequestBodyFormat> {
        let mut headers = Headers::new(&self.buf[self.pos..]);
        let mut body = RequestBodyHeaders::default();

        for hdr in &mut headers {
            let hdr = hdr.map_err(|err| match err {
                uhttp_request::Error::Partial =>
                    StatusCode::RequestHeaderFieldsTooLarge,
                uhttp_request::Error::Syntax =>
                    StatusCode::BadRequest,
            })?;

            try!(body.process_header(&hdr));
        }

        self.pos = subslice_index(&self.buf[..], headers.into_inner());

        body.into_format()
    }

    /// Consume the object and extract the underlying stream.
    pub fn into_stream(self) -> S { self.stream }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::io::Cursor;

    #[test]
    fn test_req_body_headers() {
        let h = RequestBodyHeaders::default();
        assert_eq!(h.into_format(), Ok(RequestBodyFormat::Closed));

        let mut h = RequestBodyHeaders::default();
        h.process_header(&Header { name: "Host", val: b"example.com" }).unwrap();
        assert_eq!(h.into_format(), Ok(RequestBodyFormat::Closed));

        let mut h = RequestBodyHeaders::default();
        assert_eq!(h.process_header(&Header { name: "Content-Encoding", val: b"identity" }),
            Ok(()));
        assert_eq!(h.process_header(&Header { name: "Content-Encoding", val: b"gzip" }),
            Err(StatusCode::NotImplemented));

        let mut h = RequestBodyHeaders::default();
        h.process_header(&Header { name: "transfer-encoding", val: b"chunked" }).unwrap();
        assert_eq!(h.into_format(), Ok(RequestBodyFormat::Chunked));

        let mut h = RequestBodyHeaders::default();
        h.process_header(&Header { name: "Transfer-Encoding", val: b"chunked" }).unwrap();
        h.process_header(&Header { name: "Content-Type", val: b"application/json" }).unwrap();
        assert_eq!(h.into_format(), Ok(RequestBodyFormat::Chunked));

        let mut h = RequestBodyHeaders::default();
        assert_eq!(h.process_header(&Header {
            name: "Content-Type",
            val: b"application/json; charset=UTF-8",
        }), Ok(()));
        assert_eq!(h.process_header(&Header {
            name: "Content-Type",
            val: b"application/json; charset=latin-1",
        }), Err(StatusCode::NotImplemented));

        let mut h = RequestBodyHeaders::default();
        h.process_header(&Header { name: "Transfer-Encoding", val: b"chunked" }).unwrap();
        assert_eq!(h.process_header(&Header { name: "Content-Type", val: b"text/plain" }),
            Err(StatusCode::NotImplemented));

        let mut h = RequestBodyHeaders::default();
        assert_eq!(h.process_header(&Header {
            name: "Transfer-Encoding",
            val: b"chunked, chunked"
        }), Err(StatusCode::NotImplemented));

        let mut h = RequestBodyHeaders::default();
        assert_eq!(h.process_header(&Header { name: "Transfer-Encoding", val: b"chunked" }),
            Ok(()));
        assert_eq!(h.process_header(&Header { name: "Transfer-Encoding", val: b"chunked" }),
            Err(StatusCode::NotImplemented));
        assert_eq!(h.into_format(), Ok(RequestBodyFormat::Chunked));

        let mut h = RequestBodyHeaders::default();
        h.process_header(&Header { name: "Transfer-Encoding", val: b"chunked" }).unwrap();
        h.process_header(&Header { name: "Content-Length", val: b"42" }).unwrap();
        assert_eq!(h.into_format(), Err(StatusCode::BadRequest));

        let mut h = RequestBodyHeaders::default();
        h.process_header(&Header { name: "Transfer-Encoding", val: b"chunked" }).unwrap();
        assert_eq!(h.process_header(&Header { name: "Content-Length", val: b"abc" }),
            Err(StatusCode::BadRequest));

        let mut h = RequestBodyHeaders::default();
        h.process_header(&Header { name: "Content-Length", val: b"1337" }).unwrap();
        assert_eq!(h.into_format(), Ok(RequestBodyFormat::Sized(1337)));
    }

    #[test]
    fn test_http_req() {
        #[derive(Eq, PartialEq, Debug)]
        enum Route {
            First,
            Second,
        }

        #[derive(Eq, PartialEq, Debug, Deserialize)]
        struct Item {
            abc: u32,
        }

        impl<'a> std::convert::TryFrom<HttpResource<'a>> for Route {
            type Err = StatusCode;
            fn try_from(r: HttpResource<'a>) -> HttpResult<Self> {
                match r.path {
                    "/first" => Ok(Route::First),
                    "/sec" => Ok(Route::Second),
                    _ => Err(StatusCode::NotFound),
                }
            }
        }

        let stream = b"GET /first HTTP/1.1\r\n\r\n{\"abc\": 123}";
        let mut cursor = Cursor::new(&stream[..]);
        let mut buf = [0; 32];
        let mut req = HttpRequest::new(&mut cursor, &mut buf[..]).unwrap();
        let (ver, method, route) = req.route::<Route>().unwrap();
        assert_eq!(ver, HttpVersion::from_parts(1, 1));
        assert_eq!(method, Method::Get);
        assert_eq!(route, Route::First);
        assert_eq!(req.read_json(), Ok(Item { abc: 123 }));

        let stream = b"GET /first HTTP/1.1\r\n\r\n{\"abc\": 123}";
        let mut buf = [0; 32];
        let mut req = HttpRequest::new(Cursor::new(&stream[..]), &mut buf[..]).unwrap();
        let (ver, method, route) = req.route::<Route>().unwrap();
        assert_eq!(ver, HttpVersion::from_parts(1, 1));
        assert_eq!(method, Method::Get);
        assert_eq!(route, Route::First);
        assert_eq!(req.read_json(), Ok(Item { abc: 123 }));
        req.into_stream();

        let stream = b"GET /first HTTP/1.1\r\n\r\n";
        let mut cursor = Cursor::new(&stream[..]);
        let mut buf = [0; 32];
        let mut req = HttpRequest::new(&mut cursor, &mut buf[..]).unwrap();
        let (ver, method, route) = req.route::<Route>().unwrap();
        assert_eq!(ver, HttpVersion::from_parts(1, 1));
        assert_eq!(method, Method::Get);
        assert_eq!(route, Route::First);
        assert_eq!(req.read_json::<Item>(), Err(StatusCode::BadRequest));

        let stream = b"PSHT HTTP/1.1\r\n\r\n";
        let mut cursor = Cursor::new(&stream[..]);
        let mut buf = [0; 32];
        let mut req = HttpRequest::new(&mut cursor, &mut buf[..]).unwrap();
        assert_eq!(req.route::<Route>(), Err(StatusCode::BadRequest));

        let stream = b"GET /path HTTP/1.1\r\n\r\n";
        let mut cursor = Cursor::new(&stream[..]);
        let mut buf = [0; 32];
        let mut req = HttpRequest::new(&mut cursor, &mut buf[..]).unwrap();
        assert_eq!(req.route::<Route>(), Err(StatusCode::NotFound));

        let stream = b"POST /sec HTTP/1.1\r\nContent-Length: 12\r\n\r\n{\"abc\": 123}";
        let mut cursor = Cursor::new(&stream[..]);
        let mut buf = [0; 8];
        let mut req = HttpRequest::new(&mut cursor, &mut buf[..]).unwrap();
        assert_eq!(req.route::<Route>(), Err(StatusCode::UriTooLong));

        let stream = b"POST /sec HTTP/1.1\r\nContent-Length: 12\r\n\r\n{\"abc\": 123}";
        let mut cursor = Cursor::new(&stream[..]);
        let mut buf = [0; 24];
        let mut req = HttpRequest::new(&mut cursor, &mut buf[..]).unwrap();
        let (ver, method, route) = req.route::<Route>().unwrap();
        assert_eq!(ver, HttpVersion::from_parts(1, 1));
        assert_eq!(method, Method::Post);
        assert_eq!(route, Route::Second);
        assert_eq!(req.read_json::<Item>(),
            Err(StatusCode::RequestHeaderFieldsTooLarge));

        let stream = b"POST /sec HTTP/1.1\r\nContent-Length: 12\r\n\r\n{\"abc\": 123}";
        let mut cursor = Cursor::new(&stream[..]);
        let mut buf = [0; 256];
        let mut req = HttpRequest::new(&mut cursor, &mut buf[..]).unwrap();
        let (ver, method, route) = req.route::<Route>().unwrap();
        assert_eq!(ver, HttpVersion::from_parts(1, 1));
        assert_eq!(method, Method::Post);
        assert_eq!(route, Route::Second);
        assert_eq!(req.read_json(), Ok(Item { abc: 123 }));

        let stream = b"POST /sec HTTP/1.1\r\nTransfer-Encoding:
            chunked\r\n\r\nc\r\n{\"abc\": 123}\r\n";
        let mut cursor = Cursor::new(&stream[..]);
        let mut buf = [0; 256];
        let mut req = HttpRequest::new(&mut cursor, &mut buf[..]).unwrap();
        let (ver, method, route) = req.route::<Route>().unwrap();
        assert_eq!(ver, HttpVersion::from_parts(1, 1));
        assert_eq!(method, Method::Post);
        assert_eq!(route, Route::Second);
        assert_eq!(req.read_json(), Ok(Item { abc: 123 }));
    }
}
