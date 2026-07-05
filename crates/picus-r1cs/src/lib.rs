pub mod grammar;
pub mod parser;

#[cfg(feature = "testkit")]
pub mod testkit;



/// Parse a variable name like "x3" or "y12" into its numeric index.
/// Returns `None` if the name doesn't match the expected pattern.
#[must_use]
pub fn parse_var_index(name: &str) -> Option<usize> {
    let first = name.as_bytes().first()?;
    if (*first == b'x' || *first == b'y') && name.len() > 1 {
        name[1..].parse().ok()
    } else {
        None
    }
}

#[cfg(test)]
#[path = "lib_tests.rs"]
mod tests;
