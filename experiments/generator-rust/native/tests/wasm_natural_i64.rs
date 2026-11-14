use generator_rust::wasm::{replay, sized_config};
use generator_rust::wasm::natural;

#[path = "../src/wasm_choice_serialization.rs"]
mod wasm_choice_serialization;
#[path = "../src/wasm_serialization.rs"]
mod wasm_serialization;

use generator_rust::wasm::choices::{Source, Tape};

#[test]
fn full_replay_preserves_natural_i64_constants() {
    for number in [0u128, 1, 1 << 32, 1 << 64, 1 << 80, (1 << 80) + 5] {
        let mut cells: Vec<u64> = vec![1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0];
        if number == 0 {
            cells.push(0);
        } else {
            cells.push(1u64 << 32);
            let mut rest: u128 = number;
            while rest > 1 {
                cells.push(if rest % 2 == 0 { 1 } else { 2 });
                rest /= 2;
            }
            cells.push(0);
        }
        cells.push(0);
        let offset: u64 = u64::try_from(cells.len()).expect("test tape length fits u64");
        let expected_trace: String = format!("[{}]",
            cells.iter().map(u64::to_string).collect::<Vec<String>>().join(","));
        let tape: Tape = cells.into_iter().rev().fold(Tape::Empty,
            |tail, head| Tape::Cons(head, Box::new(tail)));
        let mut config = sized_config(0, offset + 1);
        config.max_types = natural::from_u64(1);
        config.max_functions = natural::from_u64(1);
        config.max_results = natural::from_u64(1);
        let (module, final_state) = match replay(config, tape) {
            Ok(output) => output,
            Err(error) => panic!("full replay must construct I64 {number}: {}",
                wasm_serialization::error_message(error)),
        };
        assert!(matches!(final_state.remaining, natural::Natural::Zero));
        match final_state.source {
            Source::Replay(Tape::Empty, actual) =>
                assert_eq!(wasm_choice_serialization::natural_decimal(&actual), offset.to_string()),
            _ => panic!("full replay must consume the exact I64 {number} tape"),
        }
        assert_eq!(wasm_choice_serialization::trace_json(&final_state.trace), expected_trace);
        let output: String = wasm_serialization::module_json(&module);
        assert!(output.contains(&format!("\"BODY\":[{{\"CONST\":{{\"I64\":{}}}}}]", number)));
    }
}
