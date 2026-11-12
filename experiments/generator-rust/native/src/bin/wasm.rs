use generator_rust::wasm::{replay, sample, sized_config, Config};
#[path = "../wasm_serialization.rs"]
mod wasm_serialization;

fn decimal(label: &str, text: &str) -> Result<u64, String> {
    if text.is_empty() || !text.bytes().all(|byte| byte.is_ascii_digit()) {
        return Err(format!("{label}={text:?} must be an unsigned decimal integer"));
    }
    text.parse::<u64>().map_err(|error| format!("{label}={text:?} exceeds u64: {error}"))
}

fn config(arguments: &[String]) -> Result<Config, String> {
    let labels: [&str; 8] = ["MAX_TYPES", "MAX_FUNCTIONS", "MAX_PARAMETERS", "MAX_RESULTS",
        "MAX_LOCALS", "MAX_EXPORTS", "FUEL", "WORK"];
    let mut values: Vec<u64> = Vec::new();
    for (label, argument) in labels.iter().zip(arguments) {
        values.push(decimal(label, argument)?);
    }
    // These are CLI safety rejections, not silent core saturation.
    if values[..6].iter().any(|value| *value > 64) || values[6] > 128 || values[7] > 1_000_000 {
        return Err("CLI resource limit: maxima <= 64, FUEL <= 128, WORK <= 1000000 required".to_owned());
    }
    Ok(Config { max_types: values[0] as usize, max_functions: values[1] as usize,
        max_parameters: values[2] as usize, max_results: values[3] as usize,
        max_locals: values[4] as usize, max_exports: values[5] as usize,
        fuel: values[6] as usize, work_limit: values[7] })
}

fn run(arguments: &[String]) -> Result<(), String> {
    if arguments.len() == 3 {
        let count: u64 = decimal("COUNT", &arguments[0])?;
        let size: u64 = decimal("SIZE", &arguments[1])?;
        let seed: u64 = decimal("SEED", &arguments[2])?;
        if count == 0 || count > 1024 || size > 32 || seed.checked_add(count - 1).is_none() {
            return Err("CLI resource limit: COUNT in 1..1024, SIZE in 0..32, SEED+COUNT-1 <= u64::MAX required".to_owned());
        }
        for index in 0..count {
            let (module, _) = sample(sized_config(size as usize, 100_000), seed + index)
                .map_err(wasm_serialization::error_message)?;
            println!("{}", wasm_serialization::module_json(&module));
        }
        return Ok(());
    }
    if arguments.len() != 10 {
        return Err("Expected COUNT SIZE SEED, or sample/replay MAX_TYPES MAX_FUNCTIONS MAX_PARAMETERS MAX_RESULTS MAX_LOCALS MAX_EXPORTS FUEL WORK SEED/TAPE_CSV ('-' for empty tape)".to_owned());
    }
    let config: Config = config(&arguments[1..9])?;
    let result = match arguments[0].as_str() {
        "sample" => sample(config, decimal("SEED", &arguments[9])?),
        "replay" => {
            let mut tape: Vec<u64> = Vec::new();
            if arguments[9] != "-" {
                for cell in arguments[9].split(',') {
                    tape.push(decimal("TAPE_CELL", cell)?);
                }
            }
            if tape.len() > 1_000_000 {
                return Err("CLI resource limit: tape must have at most 1000000 cells".to_owned());
            }
            replay(config, tape)
        }
        command => return Err(format!("Unknown command {command:?}; expected sample or replay")),
    };
    let (module, choices) = result.map_err(wasm_serialization::error_message)?;
    println!("{}", wasm_serialization::report_json(&module, &choices));
    Ok(())
}

fn main() -> Result<(), String> {
    run(&std::env::args().skip(1).collect::<Vec<String>>())
}
