use generator_comparison_rust::ast::{Expr, ValueType, expression_json, root_type, type_name};
use generator_comparison_rust::cli::{Options, parse_options};
use generator_comparison_rust::generator::generate;
use std::io::{BufWriter, Write};
use std::process::ExitCode;

fn sample(options: &Options) -> std::io::Result<()> {
    let mut output: BufWriter<std::io::StdoutLock<'_>> = BufWriter::new(std::io::stdout().lock());
    for index in 0..options.count {
        let value_type: ValueType = root_type(index);
        let (expr, _): (Expr, u64) = generate(value_type, options.nodes, &[], options.seed + index);
        writeln!(
            output,
            "{{\"index\":{index},\"type\":\"{}\",\"expr\":{}}}",
            type_name(value_type),
            expression_json(&expr),
        )?;
    }
    output.flush()
}

fn main() -> ExitCode {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let options: Options = match parse_options(&arguments) {
        Ok(options) => options,
        Err(error) => {
            eprintln!("sample arguments rejected: {error}");
            return ExitCode::FAILURE;
        }
    };
    match sample(&options) {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("sample JSON output failed: {error}");
            ExitCode::FAILURE
        }
    }
}
