use generator_comparison_rust::ast::{Expr, Inspection, fold_digest, inspect, root_type};
use generator_comparison_rust::cli::{Options, parse_options};
use generator_comparison_rust::generator::generate;
use std::io::Write;
use std::process::ExitCode;
use std::time::Instant;

struct Benchmark {
    total_nodes: u64,
    checksum: u64,
    elapsed_ns: u128,
}

fn benchmark(options: &Options) -> Benchmark {
    let mut total_nodes: u64 = 0;
    let mut checksum: u64 = 0;
    let start: Instant = Instant::now();
    for index in 0..options.count {
        let (expr, _): (Expr, u64) =
            generate(root_type(index), options.nodes, &[], options.seed + index);
        let inspected: Inspection = inspect(&expr);
        total_nodes += inspected.nodes;
        checksum = fold_digest(checksum, inspected.digest);
    }
    let elapsed_ns: u128 = start.elapsed().as_nanos();
    Benchmark { total_nodes, checksum, elapsed_ns }
}

fn main() -> ExitCode {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let options: Options = match parse_options(&arguments) {
        Ok(options) => options,
        Err(error) => {
            eprintln!("bench arguments rejected: {error}");
            return ExitCode::FAILURE;
        }
    };
    let result: Benchmark = benchmark(&options);
    let output: std::io::Result<()> = writeln!(
        std::io::stdout().lock(),
        "{{\"count\":{},\"nodes\":{},\"seed\":{},\"total_nodes\":{},\"checksum\":{},\"elapsed_ns\":{}}}",
        options.count, options.nodes, options.seed, result.total_nodes, result.checksum, result.elapsed_ns,
    );
    match output {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("benchmark JSON output failed: {error}");
            ExitCode::FAILURE
        }
    }
}
