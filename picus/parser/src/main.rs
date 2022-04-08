use std::env;
// use crate::VERSION;

const VERSION: &'static str = env!("CARGO_PKG_VERSION");

fn main() {
    println!("Start to parse!");
    let args: Vec<String> = env::args().collect();
    let initial_file = args[1].to_string();
    println!("{:?}", args[1]);
 
    let result_program_archive = parser::run_parser(initial_file, VERSION);
}