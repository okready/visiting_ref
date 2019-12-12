// Copyright 2019 Theodore Cipicchio
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Library tests.

use super::*;
use alloc::format;

#[test]
fn fmt_debug_impl_works() {
    let (value, _) = VisitingMut::new(683);
    assert_eq!(format!("{:?}", value), "VisitingMut { value: 683 }");
    let value = VisitingMut::downgrade(value);
    assert_eq!(format!("{:?}", value), "VisitingRef { value: 683 }");
}

#[test]
fn fmt_display_impl_works() {
    let (value, _) = VisitingMut::new(683);
    assert_eq!(format!("{}", value), "683");
    let value = VisitingMut::downgrade(value);
    assert_eq!(format!("{}", value), "683");
}

#[test]
fn fmt_binary_impl_works() {
    let (value, _) = VisitingMut::new(683);
    assert_eq!(format!("{:b}", value), "1010101011");
    let value = VisitingMut::downgrade(value);
    assert_eq!(format!("{:b}", value), "1010101011");
}

#[test]
fn fmt_lower_exp_impl_works() {
    let (value, _) = VisitingMut::new(683.0);
    assert_eq!(format!("{:e}", value), "6.83e2");
    let value = VisitingMut::downgrade(value);
    assert_eq!(format!("{:e}", value), "6.83e2");
}

#[test]
fn fmt_lower_hex_impl_works() {
    let (value, _) = VisitingMut::new(683);
    assert_eq!(format!("{:x}", value), "2ab");
    let value = VisitingMut::downgrade(value);
    assert_eq!(format!("{:x}", value), "2ab");
}

#[test]
fn fmt_octal_impl_works() {
    let (value, _) = VisitingMut::new(683);
    assert_eq!(format!("{:o}", value), "1253");
    let value = VisitingMut::downgrade(value);
    assert_eq!(format!("{:o}", value), "1253");
}

#[test]
fn fmt_pointer_impl_works() {
    let (value, _) = VisitingMut::new(683 as usize as *const u8);
    assert_eq!(format!("{:p}", value), "0x2ab");
    let value = VisitingMut::downgrade(value);
    assert_eq!(format!("{:p}", value), "0x2ab");
}

#[test]
fn fmt_upper_exp_impl_works() {
    let (value, _) = VisitingMut::new(683.0);
    assert_eq!(format!("{:E}", value), "6.83E2");
    let value = VisitingMut::downgrade(value);
    assert_eq!(format!("{:E}", value), "6.83E2");
}

#[test]
fn fmt_upper_hex_impl_works() {
    let (value, _) = VisitingMut::new(683);
    assert_eq!(format!("{:X}", value), "2AB");
    let value = VisitingMut::downgrade(value);
    assert_eq!(format!("{:X}", value), "2AB");
}
