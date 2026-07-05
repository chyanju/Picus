//! Small shared helpers over cvc5's C FFI.
//!
//! These centralize the crate's `unsafe` raw-pointer conversions — decoding
//! C strings and collecting `(size, ptr)` array outputs — so the pattern,
//! and its safety/UTF-8 policy, lives in exactly one place instead of being
//! hand-rolled at every call site.

use std::ffi::CStr;
use std::os::raw::c_char;

/// Decode a cvc5-owned C string into an owned [`String`].
///
/// UTF-8 POLICY: cvc5's C API returns UTF-8 strings. We decode leniently —
/// any invalid byte sequence is replaced with U+FFFD (`to_string_lossy`)
/// rather than panicking.
///
/// # Safety
/// `ptr` must be non-null and point to a valid NUL-terminated C string that
/// stays live for the duration of the call.
pub(crate) unsafe fn cstr_to_string(ptr: *const c_char) -> String {
    unsafe { CStr::from_ptr(ptr) }.to_string_lossy().into_owned()
}

/// Borrow a cvc5-owned C string as `&str` without allocating.
///
/// Same lenient UTF-8 policy as [`cstr_to_string`], but non-UTF-8 input
/// yields `""` (via `to_str().unwrap_or("")`) rather than an allocated
/// replacement string.
///
/// # Safety
/// `ptr` must be non-null and point to a valid NUL-terminated C string that
/// remains live for all of `'a`.
pub(crate) unsafe fn cstr_to_str<'a>(ptr: *const c_char) -> &'a str {
    unsafe { CStr::from_ptr(ptr) }.to_str().unwrap_or("")
}

/// Collect `size` elements of a raw C array at `ptr`, mapping each raw
/// element through `f`.
///
/// Centralizes the `(0..size).map(|i| f(*ptr.add(i))).collect()` pattern
/// used to wrap cvc5's `(size, ptr)` array getters. Accepts `*const` or
/// `*mut` (the latter coerces).
///
/// # Safety
/// `ptr` must point to at least `size` consecutive initialized `R` values
/// (or `size` must be 0). `ptr` and `size` are typically the paired outputs
/// of a single cvc5 getter.
pub(crate) unsafe fn collect_raw_array<R: Copy, W>(
    ptr: *const R,
    size: usize,
    f: impl Fn(R) -> W,
) -> Vec<W> {
    (0..size).map(|i| f(unsafe { *ptr.add(i) })).collect()
}
