use std::borrow::Cow;
use std::fmt;

use http::{HeaderMap as HttpHeaderMap, header::AsHeaderName};
use http::HeaderValue;
use http::header::HeaderName;

use crate::uncased::{Uncased, UncasedStr};

/// Simple representation of an HTTP header.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Header<'h> {
    /// The name of the header.
    pub name: Uncased<'h>,
    /// The value of the header.
    pub value: Cow<'h, str>,
}

impl<'h> Header<'h> {
    /// Constructs a new header. This method should be used rarely and only for
    /// non-standard headers. Instead, prefer to use the `Into<Header>`
    /// implementations of many types, including
    /// [`ContentType`](crate::ContentType) and all of the headers in
    /// [`http::hyper::header`](hyper::header).
    ///
    /// # Examples
    ///
    /// Create a custom header with name `X-Custom-Header` and value `custom
    /// value`.
    ///
    /// ```rust
    /// # extern crate rocket;
    /// use rocket::http::Header;
    ///
    /// let header = Header::new("X-Custom-Header", b"custom value");
    /// assert_eq!(header.to_string().unwrap(), "X-Custom-Header: custom value");
    /// ```
    ///
    /// Use a `String` as a value to do the same.
    ///
    /// ```rust
    /// # extern crate rocket;
    /// use rocket::http::Header;
    ///
    /// let value = format!("{} value", "custom");
    /// let header = Header::new("X-Custom-Header", value);
    /// assert_eq!(header.to_string(), "X-Custom-Header: custom value");
    /// ```
    #[inline(always)]
    pub fn new<'a: 'h, 'b: 'h, N, V>(name: N, value: V) -> Header<'h>
        where N: Into<Cow<'a, str>>, V: Into<Cow<'b, str>>
    {
        Header {
            name: Uncased::new(name),
            value: value.into()
        }
    }

    /// Returns the name of this header.
    ///
    /// # Example
    ///
    /// A case-sensitive equality check:
    ///
    /// ```rust
    /// # extern crate rocket;
    /// use rocket::http::Header;
    ///
    /// let value = format!("{} value", "custom");
    /// let header = Header::new("X-Custom-Header", value);
    /// assert_eq!(header.name().as_str(), "X-Custom-Header");
    /// assert_ne!(header.name().as_str(), "X-CUSTOM-HEADER");
    /// ```
    ///
    /// A case-insensitive equality check:
    ///
    /// ```rust
    /// # extern crate rocket;
    /// use rocket::http::Header;
    ///
    /// let header = Header::new("X-Custom-Header", "custom value");
    /// assert_eq!(header.name(), "X-Custom-Header");
    /// assert_eq!(header.name(), "X-CUSTOM-HEADER");
    /// ```
    #[inline(always)]
    pub fn name(&self) -> &UncasedStr {
        &self.name
    }

    /// Returns the value of this header.
    ///
    /// # Example
    ///
    /// A case-sensitive equality check:
    ///
    /// ```rust
    /// # extern crate rocket;
    /// use rocket::http::Header;
    ///
    /// let header = Header::new("X-Custom-Header", "custom value");
    /// assert_eq!(header.value(), "custom value");
    /// ```
    #[inline(always)]
    pub fn value(&self) -> &str {
        &self.value
    }
}

impl fmt::Display for Header<'_> {
    #[inline(always)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.name, self.value)
    }
}

/// A collection of headers, mapping a header name to its many ordered values.
///
/// # Case-Insensitivity
///
/// All header names, including those passed in to `HeaderMap` methods and those
/// stored in an existing `HeaderMap`, are treated case-insensitively. This
/// means that, for instance, a look for a header by the name of "aBC" will
/// returns values for headers of names "AbC", "ABC", "abc", and so on.
#[derive(Clone, Debug, PartialEq, Default)]
pub struct HeaderMap {
    headers: HttpHeaderMap
}

impl HeaderMap {
    /// Returns an empty header collection.
    ///
    /// # Example
    ///
    /// ```rust
    /// # extern crate rocket;
    /// use rocket::http::HeaderMap;
    ///
    /// let map = HeaderMap::new();
    /// ```
    #[inline(always)]
    pub fn new() -> HeaderMap {
        HeaderMap { headers: HttpHeaderMap::new() }
    }

    /// Returns true if `self` contains a header with the name `name`.
    ///
    /// # Example
    ///
    /// ```rust
    /// # extern crate rocket;
    /// use rocket::http::{HeaderMap, ContentType};
    ///
    /// let mut map = HeaderMap::new();
    /// map.add(ContentType::HTML);
    ///
    /// assert!(map.contains("Content-Type"));
    /// assert!(!map.contains("Accepts"));
    /// ```
    #[inline]
    pub fn contains(&self, name: &str) -> bool {
        self.headers.contains_key(name)
    }

    /// Returns the number of _values_ stored in the map.
    ///
    /// # Example
    ///
    /// ```rust
    /// # extern crate rocket;
    /// use rocket::http::HeaderMap;
    ///
    /// let mut map = HeaderMap::new();
    /// assert_eq!(map.len(), 0);
    ///
    /// map.add_raw("X-Custom", "value_1");
    /// assert_eq!(map.len(), 1);
    ///
    /// map.replace_raw("X-Custom", "value_2");
    /// assert_eq!(map.len(), 1);
    ///
    /// map.add_raw("X-Custom", "value_1");
    /// assert_eq!(map.len(), 2);
    /// ```
    #[inline]
    pub fn len(&self) -> usize {
        self.headers.len()
    }

    /// Returns `true` if there are no headers stored in the map. Otherwise
    /// returns `false`.
    ///
    /// # Example
    ///
    /// ```rust
    /// # extern crate rocket;
    /// use rocket::http::HeaderMap;
    ///
    /// let map = HeaderMap::new();
    /// assert!(map.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.headers.is_empty()
    }

    /// Returns an iterator over all of the values stored in `self` for the
    /// header with name `name`. The headers are returned in FIFO order.
    ///
    /// # Example
    ///
    /// ```rust
    /// # extern crate rocket;
    /// use rocket::http::HeaderMap;
    ///
    /// let mut map = HeaderMap::new();
    /// map.add_raw("X-Custom", "value_1");
    /// map.add_raw("X-Custom", "value_2");
    ///
    /// assert_eq!(map.len(), 2);
    ///
    /// let mut values = map.get("X-Custom");
    /// assert_eq!(values.next().unwrap(), "value_1");
    /// assert_eq!(values.next().unwrap(), "value_2");
    /// assert_eq!(values.next(), None);
    /// ```
    #[inline]
    pub fn get<K>(&self, name: K) -> impl Iterator<Item=&HeaderValue>
        where
            K: AsHeaderName {
        self.headers
            .get_all(name)
            .into_iter()
    }

    /// Returns the _first_ value stored for the header with name `name` if
    /// there is one.
    ///
    /// # Examples
    ///
    /// Retrieve the first value when one exists:
    ///
    /// ```rust
    /// # extern crate rocket;
    /// use rocket::http::HeaderMap;
    ///
    /// let mut map = HeaderMap::new();
    /// map.add_raw("X-Custom", "value_1");
    /// map.add_raw("X-Custom", "value_2");
    ///
    /// assert_eq!(map.len(), 2);
    ///
    /// let first_value = map.get_one("X-Custom");
    /// assert_eq!(first_value.uwrap(), "value_1");
    /// ```
    ///
    /// Attempt to retrieve a value that doesn't exist:
    ///
    /// ```rust
    /// # extern crate rocket;
    /// use rocket::http::HeaderMap;
    ///
    /// let mut map = HeaderMap::new();
    /// map.add_raw("X-Custom", "value_1");
    ///
    /// let first_value = map.get_one("X-Other");
    /// assert_eq!(first_value, None);
    /// ```
    #[inline]
    pub fn get_one<'a>(&'a self, name: &str) -> Option<&'a [u8]> {
        self.headers.get(name)
            .map(|value| value.as_bytes())
    }

    /// Replace any header that matches the name of `header.name` with `header`.
    /// If there is no such header in `self`, add `header`. If the matching
    /// header had multiple values, all of the values are removed, and only the
    /// value in `header` will remain.
    ///
    /// # Example
    ///
    /// Replace a header that doesn't yet exist:
    ///
    /// ```rust
    /// # extern crate rocket;
    /// use rocket::http::{HeaderMap, ContentType};
    ///
    /// let mut map = HeaderMap::new();
    /// map.replace(ContentType::JSON);
    ///
    /// assert!(map.get_one("Content-Type").is_some());
    /// ```
    ///
    /// Replace a header that already exists:
    ///
    /// ```rust
    /// # extern crate rocket;
    /// use rocket::http::{HeaderMap, ContentType};
    ///
    /// let mut map = HeaderMap::new();
    ///
    /// map.replace(ContentType::JSON);
    /// assert_eq!(map.get_one("Content-Type").unwrap(), "application/json");
    ///
    /// map.replace(ContentType::GIF);
    /// assert_eq!(map.get_one("Content-Type").unwrap(), "image/gif");
    /// assert_eq!(map.len(), 1);
    /// ```
    ///
    /// An example of case-insensitivity.
    ///
    /// ```rust
    /// # extern crate rocket;
    /// use rocket::http::{HeaderMap, Header, ContentType};
    ///
    /// let mut map = HeaderMap::new();
    ///
    /// map.replace(ContentType::JSON);
    /// assert_eq!(map.get_one("Content-Type").unwrap(), "application/json");
    ///
    /// map.replace(Header::new("CONTENT-type", "image/gif"));
    /// assert_eq!(map.get_one("Content-Type").unwrap(), "image/gif");
    /// assert_eq!(map.len(), 1);
    /// ```
    #[inline(always)]
    pub fn replace<'p, H: Into<Header<'p>>>(&mut self, header: H) -> bool {
        let header = header.into();
        let maybe_value = HeaderValue::from_str(&header.value);
        let value = maybe_value.unwrap(); // TODO: Review, please - how to del with application which passes in a value HeaderMap won't accept
        let name = HeaderName::from_bytes(header.name.string.as_bytes());
        self.headers.insert(name.unwrap(), value).is_some() // TODO: Review, please - how to del with application which passes in a header name which won't pass as a header
    }

    /// A convenience method to replace a header using a raw name and value.
    /// Aliases `replace(Header::new(name, value))`. Should be used rarely.
    ///
    /// # Example
    ///
    /// ```rust
    /// # extern crate rocket;
    /// use rocket::http::HeaderMap;
    ///
    /// let mut map = HeaderMap::new();
    ///
    /// map.replace_raw("X-Custom", "value_1");
    /// assert_eq!(map.get_one("X-Custom"), Some("value_1"));
    ///
    /// map.replace_raw("X-Custom", "value_2");
    /// assert_eq!(map.get_one("X-Custom"), Some("value_2"));
    /// assert_eq!(map.len(), 1);
    /// ```
    #[inline(always)]
    pub fn replace_raw<'a, 'b, N, V>(&mut self, name: N, value: V) -> bool
        where N: Into<Cow<'a, str>>, V: Into<Cow<'b, str>>
    {
        self.replace(Header::new(name, value))
    }

    /// Replaces all of the values for a header with name `name` with `values`.
    /// This a low-level method and should rarely be used.
    ///
    ///
    /// # Example
    ///
    /// ```rust
    /// # extern crate rocket;
    /// use rocket::http::HeaderMap;
    ///
    /// let mut map = HeaderMap::new();
    /// map.add_raw("X-Custom", "value_1");
    /// map.add_raw("X-Custom", "value_2");
    ///
    /// let vals: Vec<_> = map.get("X-Custom").map(|s| s.to_string()).collect();
    /// assert_eq!(vals, vec!["value_1", "value_2"]);
    ///
    /// map.replace_all("X-Custom", vec!["value_3".into(), "value_4".into()]);
    /// let vals: Vec<_> = map.get("X-Custom").collect();
    /// assert_eq!(vals, vec!["value_3", "value_4"]);
    /// ```
    #[inline(always)]
    pub fn replace_all<'n, 'v, H>(&mut self, name: H, values: Vec<Cow<'v, str>>)
        where H: Into<Cow<'n, str>>
    {
        let name = name.into();
        let name = name.as_bytes();
        if values.is_empty() {
            // Just wipe all previous values
            while self.headers.remove(HeaderName::from_bytes(name).unwrap()).is_some() {
            }
        } else {
            // insert the first, append the rest
            let value = HeaderValue::from_str(&values[0]).unwrap(); // TODO
            self.headers.insert(HeaderName::from_bytes(name).unwrap(), value);

            for value in values[1..].iter() {
                let value = HeaderValue::from_str(value).unwrap(); // TODO
                self.headers.insert(HeaderName::from_bytes(name).unwrap(), value);
            }
        }
    }

    /// Adds `header` into the map. If a header with `header.name` was
    /// previously added, that header will have one more value.
    ///
    /// ```rust
    /// # extern crate rocket;
    /// use rocket::http::{Cookie, HeaderMap};
    ///
    /// let mut map = HeaderMap::new();
    ///
    /// map.add(&Cookie::new("a", "b"));
    /// assert_eq!(map.get("Set-Cookie").count(), 1);
    ///
    /// map.add(&Cookie::new("c", "d"));
    /// assert_eq!(map.get("Set-Cookie").count(), 2);
    /// ```
    #[inline(always)]
    pub fn add<'p, H: Into<Header<'p>>>(&mut self, header: H) {
        let header = header.into();
        let name = header.name.string.as_bytes(); // TODO
         // TODO
        let value = HeaderValue::from_str(&header.value).unwrap(); // TODO
        if self.headers.contains_key(header.name.string.as_ref()) { 
            self.headers.append(HeaderName::from_bytes(name).unwrap(), value);
        } else {
            self.headers.insert(HeaderName::from_bytes(name).unwrap(), value);
        }
    }

    /// A convenience method to add a header using a raw name and value.
    /// Aliases `add(Header::new(name, value))`. Should be used rarely.
    ///
    /// # Example
    ///
    /// ```rust
    /// # extern crate rocket;
    /// use rocket::http::HeaderMap;
    ///
    /// let mut map = HeaderMap::new();
    ///
    /// map.add_raw("X-Custom", "value_1");
    /// assert_eq!(map.get("X-Custom").count(), 1);
    ///
    /// map.add_raw("X-Custom", "value_2");
    /// let values: Vec<_> = map.get("X-Custom").collect();
    /// assert_eq!(values, vec!["value_1", "value_2"]);
    /// ```
    #[inline(always)]
    pub fn add_raw<'a, 'b, N, V>(&mut self, name: N, value: V)
        where N: Into<Cow<'a, str>>, V: Into<Cow<'b, str>>
    {
        self.add(Header::new(name, value))
    }

    /// Adds all of the values to a header with name `name`. This a low-level
    /// method and should rarely be used. `values` will be empty when this
    /// method returns.
    ///
    /// # Example
    ///
    /// ```rust
    /// # extern crate rocket;
    /// use rocket::http::HeaderMap;
    ///
    /// let mut map = HeaderMap::new();
    ///
    /// let mut values = vec!["value_1".into(), "value_2".into()];
    /// map.add_all("X-Custom", &mut values);
    /// assert_eq!(map.get("X-Custom").count(), 2);
    /// assert_eq!(values.len(), 0);
    ///
    /// let mut values = vec!["value_3".into(), "value_4".into()];
    /// map.add_all("X-Custom", &mut values);
    /// assert_eq!(map.get("X-Custom").count(), 4);
    /// assert_eq!(values.len(), 0);
    ///
    /// let values: Vec<_> = map.get("X-Custom").collect();
    /// assert_eq!(values, vec!["value_1", "value_2", "value_3", "value_4"]);
    /// ```
    #[inline(always)]
    pub fn add_all<'n, H>(&mut self, name: H, values: &mut Vec<Cow<'_, str>>)
        where H: Into<Cow<'n, str>>
    {
        let name = name.into();
        // TODO: This does a lot of unneccesary copying, but it just a test of the API
        let new_values = std::mem::replace(values, Vec::new());
        for value in new_values {
            self.add_raw(name.as_ref(), value);
        }
    }

    pub fn take_http_headers(&mut self) -> HttpHeaderMap {
        std::mem::replace(&mut self.headers, HttpHeaderMap::new())
    }

    /// Remove all of the values for header with name `name`.
    ///
    /// # Example
    ///
    /// ```rust
    /// # extern crate rocket;
    /// use rocket::http::HeaderMap;
    ///
    /// let mut map = HeaderMap::new();
    /// map.add_raw("X-Custom", "value_1");
    /// map.add_raw("X-Custom", "value_2");
    /// map.add_raw("X-Other", "other");
    ///
    /// assert_eq!(map.len(), 3);
    ///
    /// map.remove("X-Custom");
    /// assert_eq!(map.len(), 1);
    #[inline(always)]
    pub fn remove(&mut self, name: &str) {
        while self.headers.remove(name).is_some() {
        }
    }

    /// Removes all of the headers stored in this map and returns a vector
    /// containing them. Header names are returned in no specific order, but all
    /// values for a given header name are grouped together, and values are in
    /// FIFO order.
    ///
    /// # Example
    ///
    /// ```rust
    /// # extern crate rocket;
    /// use rocket::http::{HeaderMap, Header};
    /// use std::collections::HashSet;
    ///
    /// // The headers we'll be storing.
    /// let all_headers = vec![
    ///     Header::new("X-Custom", "value_1"),
    ///     Header::new("X-Custom", "value_2"),
    ///     Header::new("X-Other", "other")
    /// ];
    ///
    /// // Create a map, store all of the headers.
    /// let mut map = HeaderMap::new();
    /// for header in all_headers.clone() {
    ///     map.add(header)
    /// }
    ///
    /// assert_eq!(map.len(), 3);
    ///
    /// // Now remove them all, ensure the map is empty.
    /// let removed_headers = map.remove_all();
    /// assert!(map.is_empty());
    ///
    /// // Create two sets: what we expect and got. Ensure they're equal.
    /// let expected_set: HashSet<_> = all_headers.into_iter().collect();
    /// let actual_set: HashSet<_> = removed_headers.into_iter().collect();
    /// assert_eq!(expected_set, actual_set);
    /// ```
    #[inline(always)]
    pub fn remove_all<'h>(&'h mut self) -> Vec<Header<'h>> {
        let old_map = std::mem::replace(self, HeaderMap::new());
        old_map.into_iter().collect()
    }

    /// Returns an iterator over all of the `Header`s stored in the map. Header
    /// names are returned in no specific order, but all values for a given
    /// header name are grouped together, and values are in FIFO order.
    ///
    /// # Example
    ///
    /// ```rust
    /// # extern crate rocket;
    /// use rocket::http::{HeaderMap, Header};
    ///
    /// // The headers we'll be storing.
    /// let all_headers = vec![
    ///     Header::new("X-Custom", "value_1"),
    ///     Header::new("X-Other", "other"),
    ///     Header::new("X-Third", "third"),
    /// ];
    ///
    /// // Create a map, store all of the headers.
    /// let mut map = HeaderMap::new();
    /// for header in all_headers {
    ///     map.add(header)
    /// }
    ///
    /// // Ensure there are three headers via the iterator.
    /// assert_eq!(map.iter().count(), 3);
    ///
    /// // Actually iterate through them.
    /// for header in map.iter() {
    ///     match header.name().as_str() {
    ///         "X-Custom" => assert_eq!(header.value(), "value_1"),
    ///         "X-Other" => assert_eq!(header.value(), "other"),
    ///         "X-Third" => assert_eq!(header.value(), "third"),
    ///         _ => unreachable!("there are only three headers")
    ///     }
    /// }
    /// ```
    pub fn iter(&self) -> impl Iterator<Item=Header<'_>> {
        self.headers.iter().map(|(key, value)| {
            Header::new(key.as_str(), String::from_utf8_lossy(value.as_bytes()))
        })
    }

    /// Consumes `self` and returns an iterator over all of the `Header`s stored
    /// in the map. Header names are returned in no specific order, but all
    /// values for a given header name are grouped together, and values are in
    /// FIFO order.
    ///
    /// # Example
    ///
    /// ```rust
    /// # extern crate rocket;
    /// use rocket::http::{HeaderMap, Header};
    ///
    /// // The headers we'll be storing.
    /// let all_headers = vec![
    ///     Header::new("X-Custom", "value_1"),
    ///     Header::new("X-Other", "other"),
    ///     Header::new("X-Third", "third"),
    /// ];
    ///
    /// // Create a map, store all of the headers.
    /// let mut map = HeaderMap::new();
    /// for header in all_headers {
    ///     map.add(header)
    /// }
    ///
    /// // Ensure there are three headers via the iterator.
    /// assert_eq!(map.iter().count(), 3);
    ///
    /// // Actually iterate through them.
    /// for header in map.into_iter() {
    ///     match header.name().as_str() {
    ///         "X-Custom" => assert_eq!(header.value(), "value_1"),
    ///         "X-Other" => assert_eq!(header.value(), "other"),
    ///         "X-Third" => assert_eq!(header.value(), "third"),
    ///         _ => unreachable!("there are only three headers")
    ///     }
    /// }
    /// ```
    // TODO: Implement IntoIterator.
    #[inline(always)]
    pub fn into_iter(self) -> impl Iterator<Item=Header<'static>> {
        self.headers.into_iter().map(|(key, value)| {
            let value = String::from_utf8_lossy(value.as_bytes());
            Header::new(key.unwrap().as_str().to_owned(), value.to_string())
        })
    }

    /// Replaces headers with fresh values from Hyper
    pub fn reset_headers(&mut self, header_map: HttpHeaderMap) {
        self.headers = header_map;
    }
}

#[cfg(test)]
mod tests {
    use super::HeaderMap;

    #[test]
    fn case_insensitive_add_get() {
        let mut map = HeaderMap::new();
        map.add_raw("content-type", "application/json");

        let ct = map.get_one("Content-Type");
        assert_eq!(ct, Some("application/json".as_bytes()));

        let ct2 = map.get_one("CONTENT-TYPE");
        assert_eq!(ct2, Some("application/json".as_bytes()))
    }

    #[test]
    fn case_insensitive_multiadd() {
        let mut map = HeaderMap::new();
        map.add_raw("x-custom", "a");
        map.add_raw("X-Custom", "b");
        map.add_raw("x-CUSTOM", "c");

        let vals: Vec<_> = map.get("x-CuStOm").collect();
        assert_eq!(vals, vec!["a".as_bytes(), "b".as_bytes(), "c".as_bytes()]);
    }
}
