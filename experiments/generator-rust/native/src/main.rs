use generator_rust::generator::generate;
#[path = "../../original/src/cli.rs"]
mod cli;
mod serialization;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let options: cli::Options = cli::parse_options(&arguments)?;
    for index in 0..options.count {
        let value_type = serialization::root_type(index);
        let (expr, state) = generate(value_type, options.nodes, &[], options.seed + index);
        let checked = serialization::inspect(&expr);
        println!(
            "{{\"index\":{index},\"type\":\"{}\",\"expr\":{},\"state\":{state},\"nodes\":{},\"digest\":{}}}",
            serialization::type_name(value_type), serialization::expression_json(&expr),
            checked.nodes, checked.digest,
        );
    }
    Ok(())
}
