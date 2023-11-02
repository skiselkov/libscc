/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */
/*
 * Copyright 2023 Saso Kiselkov. All rights reserved.
 */

use std::ffi::{
    c_void, c_char,
    CString, CStr,
};
use std::{fs::File, io::Read};
use std::vec::IntoIter;
use std::iter::Peekable;

type Components = Vec<CString>;

type HandleSemicolon = extern "C" fn(comps: *const Components,
    userinfo: *mut c_void) -> bool;

fn finish_token(comps: &mut Components, token: String, filepath: &str,
    line_nr: u32) {
	comps.push(CString::new(token.as_str())
	    .unwrap_or_else(|_|panic!("{}:{}: found stray NUL byte in input",
	    filepath, line_nr)));
}

fn skip_opt_linefeed(it: &mut Peekable<IntoIter<char>>) {
	// skip a linefeed character that might be next
	if let Some(next_c) = it.peek() {
		if *next_c == '\n' {
			_ = it.next();
		}
	}
}

fn read_string_escape(it: &mut Peekable<IntoIter<char>>, token: &mut String,
    line_nr: &mut u32) {
	if let Some(esc_c) = it.next() {
		match esc_c {
		    't' => token.push('\t'),
		    'n' => token.push('\n'),
		    'r' => token.push('\r'),
		    '\r' => {
			skip_opt_linefeed(it);
			*line_nr += 1;
		    },
		    '\n' => {
			*line_nr += 1;
		    },
		    _ => token.push(esc_c),
		}
	}
}

fn read_quoted_str(it: &mut Peekable<IntoIter<char>>, token: &mut String,
    line_nr: &mut u32) {
	while let Some(c) = it.next() {
		match c {
		    '"' => break,
		    '\\' => read_string_escape(it, token, line_nr),
		    _ => token.push(c),
		}
	}
}

fn scc_read_impl(filepath: &str, cb: HandleSemicolon,
    userinfo: *mut c_void) -> Result<(), std::io::Error> {
	let mut filebuf: Vec<u8> = vec![];
	File::open(filepath)?.read_to_end(&mut filebuf)?;
	let chars: Vec<char> = filebuf
	    .iter()
	    .map(|b| char::from(*b))
	    .collect();

	let mut comps = Components::default();
	let mut token = String::new();

	let mut line_nr = 1u32;

	let mut chars_it = chars.into_iter().peekable();
	while let Some(c) = chars_it.next() {
		if c.is_ascii_whitespace() {
			if c == '\r' {
				skip_opt_linefeed(&mut chars_it);
				line_nr += 1;
			}
			if c == '\n' {
				line_nr += 1;
			}
		} else if c == '#' {
			while let Some(next_c) = chars_it.peek() {
				if *next_c == '\r' || *next_c == '\n' {
					break;
				}
				_ = chars_it.next();
			}
		} else if c == ',' {
			finish_token(&mut comps, std::mem::take(&mut token),
			    filepath, line_nr);
		} else if c == ';' {
			finish_token(&mut comps, std::mem::take(&mut token),
			    filepath, line_nr);
			cb(&comps, userinfo);
			comps = Components::default();
		} else if c == '"' {
			read_quoted_str(&mut chars_it, &mut token,
			    &mut line_nr);
		} else {
			token.push(c);
		}
	}
	Ok(())
}

fn strlcpy(out_str: *mut c_char, in_str: &str, cap: usize) {
	if out_str.is_null() {
		assert!(cap == 0);
		return;
	}
	assert!(cap != 0);
	let in_cstr = CString::new(in_str).expect("Cannot convert C string");
	let max_len = in_str.len().min(cap);
	let in_slice = &in_cstr.as_bytes_with_nul()[..max_len];
	let out_slice = unsafe {
		core::slice::from_raw_parts_mut(out_str as *mut u8, max_len)
	};
	out_slice.copy_from_slice(in_slice);
	// make sure the output is always properly NUL terminated
	out_slice[out_slice.len() - 1] = b'\0';
}

#[no_mangle]
extern "C" fn scc_read(filepath: *const c_char, cb: HandleSemicolon,
    userinfo: *mut c_void, out_err: *mut c_char, out_err_cap: usize) ->
    bool {
	assert!(!filepath.is_null());
	match scc_read_impl(unsafe{CStr::from_ptr(filepath)}
	    .to_str().expect("cannot convert C string"), cb, userinfo) {
	    Ok(_) => true,
	    Err(e) => {
		strlcpy(out_err, e.to_string().as_str(), out_err_cap);
		false
	    },
	}
}

#[no_mangle]
extern "C" fn scc_comp_count(comps: *const Components) -> usize {
	assert!(!comps.is_null());
	unsafe{&*comps}.len()
}

#[no_mangle]
extern "C" fn scc_comp_get(comps: *const Components, idx: usize) ->
    *const c_char {
	assert!(!comps.is_null());
	let comps = unsafe{&*comps};
	comps[idx].as_c_str().as_ptr()
}

mod tests {
	use crate::scc;

	#[allow(dead_code)]
	extern "C" fn semicolon_cb(comps: *const scc::Components,
	    _userinfo: *mut std::ffi::c_void) -> bool {
		assert!(!comps.is_null());
		for i in 0..scc::scc_comp_count(comps) {
			let c_str = scc::scc_comp_get(comps, i);
			let tmp = unsafe{std::ffi::CStr::from_ptr(c_str)};
			print!("\"{}\"{}", tmp.to_str().unwrap(),
			    if i == scc::scc_comp_count(comps) - 1 {
			    ";\n" } else { ", " });
		}
		true
	}
	#[test]
	fn test_parser() {
		use std::ffi::{c_char, CString, CStr};
		let filename = std::env::var("CONF")
		    .unwrap_or_else(|_|panic!(concat!("This test requires a ",
		    "\"CONF\" environment variable pointing at the test ",
		    "config file to parse. For example:\n",
		    "CONF=/tmp/my_test.conf cargo test")));
		let c_filename = CString::new(filename.as_str()).unwrap();
		let mut error = unsafe {
			std::mem::zeroed::<[c_char; 128]>()
		};
		if !scc::scc_read(c_filename.as_c_str()
		    .as_ptr(), semicolon_cb, std::ptr::null_mut(),
		    &mut error as *mut c_char, error.len()) {
			panic!("Error processing input {}: {}", filename,
			    unsafe { CStr::from_ptr(&error as *const i8) }
			    .to_str()
			    .unwrap());
		}
	}
}
