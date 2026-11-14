use generator_rust::wasm::{replay, sized_config};
use generator_rust::wasm::natural;

#[path = "../src/wasm_choice_serialization.rs"]
mod wasm_choice_serialization;
#[path = "../src/wasm_serialization.rs"]
mod wasm_serialization;

use generator_rust::wasm::choices::Tape;

#[test]
fn full_replay_preserves_natural_i32_constants() {
    for number in [0u128, 1, 1 << 32, 1 << 64, 1 << 80, (1 << 80) + 5] {
        let mut cells: Vec<u64> = vec![1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0];
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
        let tape: Tape = cells.into_iter().rev().fold(Tape::Empty,
            |tail, head| Tape::Cons(head, Box::new(tail)));
        let mut config = sized_config(0, 1000);
        config.max_types = natural::from_u64(1);
        config.max_functions = natural::from_u64(1);
        config.max_results = natural::from_u64(1);
        let (module, _) = match replay(config, tape) {
            Ok(output) => output,
            Err(_) => panic!("full replay must construct I32 {number}"),
        };
        let output: String = wasm_serialization::module_json(&module);
        assert!(output.contains(&format!("\"BODY\":[{{\"CONST\":{{\"I32\":{}}}}}]", number)));
    }
}

#[test]
fn recursive_literal_rejects_missing_and_invalid_bits() {
    use generator_rust::wasm::choices::GenerationError;
    for tail in [vec![1u64 << 32], vec![1u64 << 32, 3]] {
        let invalid_bit: bool = tail.len() == 2;
        let mut cells: Vec<u64> = vec![1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0];
        cells.extend(tail);
        let tape: Tape = cells.into_iter().rev().fold(Tape::Empty,
            |tail, head| Tape::Cons(head, Box::new(tail)));
        let mut config = sized_config(0, 1000);
        config.max_types = natural::from_u64(1);
        config.max_functions = natural::from_u64(1);
        config.max_results = natural::from_u64(1);
        match replay(config, tape) {
            Err(GenerationError::ChoiceOutOfRange(_, 3, 3)) if invalid_bit => (),
            Err(GenerationError::TapeExhausted(_)) if !invalid_bit => (),
            _ => panic!("invalid recursive literal tape must fail explicitly"),
        }
    }
}
