use std::fmt::{Display, Formatter};

pub struct Options {
    pub count: u64,
    pub nodes: usize,
    pub seed: u64,
}

#[derive(Debug)]
pub struct ArgumentError(pub String);

impl Display for ArgumentError {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(&self.0)
    }
}

impl std::error::Error for ArgumentError {}

fn decimal(name: &str, argument: &str) -> Result<u64, ArgumentError> {
    if argument.is_empty() || !argument.bytes().all(|byte| byte.is_ascii_digit()) {
        return Err(ArgumentError(format!(
            "{name}={argument:?} is not an unsigned decimal integer"
        )));
    }
    argument.parse::<u64>().map_err(|error| {
        ArgumentError(format!(
            "{name}={argument:?} cannot be represented as a 64-bit unsigned integer: {error}"
        ))
    })
}

pub fn parse_options(arguments: &[String]) -> Result<Options, ArgumentError> {
    if arguments.len() != 3 {
        return Err(ArgumentError(format!(
            "expected COUNT NODES SEED (three arguments), received {} arguments",
            arguments.len()
        )));
    }
    let count: u64 = decimal("COUNT", &arguments[0])?;
    let nodes: u64 = decimal("NODES", &arguments[1])?;
    let seed: u64 = decimal("SEED", &arguments[2])?;
    if count == 0 {
        return Err(ArgumentError("COUNT=0 is unsupported; COUNT must be at least 1".to_owned()));
    }
    if !(1..=1024).contains(&nodes) {
        return Err(ArgumentError(format!(
            "NODES={nodes} is unsupported; NODES must be between 1 and 1024"
        )));
    }
    if seed.checked_add(count - 1).is_none() {
        return Err(ArgumentError(format!(
            "SEED={seed} plus COUNT={count} minus 1 overflows the 64-bit per-sample seed"
        )));
    }
    if count.checked_mul(nodes).is_none() {
        return Err(ArgumentError(format!(
            "COUNT={count} times NODES={nodes} overflows the 64-bit total node count"
        )));
    }
    Ok(Options { count, nodes: nodes as usize, seed })
}
