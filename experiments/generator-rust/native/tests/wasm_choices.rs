use generator_rust::wasm::{replay, sized_config, AddressType, Memories};
use generator_rust::wasm::choices::{pick_natural, pick_word, word, Choices, GenerationError, Source, Tape};
use generator_rust::wasm::natural::{self, Natural, Positive};

fn power(exponent: usize) -> Natural {
    let mut value: Positive = Positive::One;
    for _ in 0..exponent {
        value = Positive::Bit0(Box::new(value));
    }
    Natural::Positive(value)
}

fn value(number: &Natural) -> u128 {
    fn positive(number: &Positive) -> u128 {
        match number {
            Positive::One => 1,
            Positive::Bit0(tail) => 2 * positive(tail),
            Positive::Bit1(tail) => 2 * positive(tail) + 1,
        }
    }
    match number {
        Natural::Zero => 0,
        Natural::Positive(number) => positive(number),
    }
}

#[test]
fn replay_and_consumption_cross_machine_counter_bounds() {
    let mut config = sized_config(0, 1);
    config.work_limit = power(80);
    let (_, state) = match replay(config, Tape::Cons(0, Box::new(Tape::Empty))) {
        Ok(result) => result,
        Err(_) => panic!("empty module must replay with a binary budget above u64"),
    };
    assert_eq!(value(&state.remaining), (1u128 << 80) - 1);
    let source = Source::Replay(Tape::Cons(u64::MAX, Box::new(Tape::Empty)), power(80));
    let choices = Choices { source, trace: Tape::Empty, remaining: power(80) };
    let (selected, state) = match word(choices) {
        Ok(result) => result,
        Err(_) => panic!("word must advance an arbitrary binary cursor"),
    };
    assert_eq!(selected, u64::MAX);
    match state.source {
        Source::Replay(Tape::Empty, offset) => assert_eq!(value(&offset), (1u128 << 80) + 1),
        _ => panic!("word must consume exactly the head cell"),
    }
    assert_eq!(value(&state.remaining), (1u128 << 80) - 1);
    assert!(matches!(state.trace, Tape::Cons(u64::MAX, _)));
}

#[test]
fn bounded_words_preserve_wide_values_and_reverse_trace() {
    let tape = Tape::Cons(281474976710656, Box::new(Tape::Cons(7, Box::new(Tape::Empty))));
    let choices = Choices { source: Source::Replay(tape, Natural::Zero),
        trace: Tape::Empty, remaining: natural::from_u64(2) };
    let (first, choices) = match pick_word(281474976710657, choices) {
        Ok(result) => result,
        Err(_) => panic!("memory64 upper page limit must remain a u64"),
    };
    let (second, choices) = match word(choices) {
        Ok(result) => result,
        Err(_) => panic!("second cell must be available"),
    };
    assert_eq!((first, second), (281474976710656, 7));
    match choices.trace {
        Tape::Cons(7, tail) => assert!(matches!(*tail, Tape::Cons(281474976710656, _))),
        _ => panic!("trace must record newest cell first"),
    }
    assert_eq!(value(&choices.remaining), 0);
}

#[test]
fn recursive_memories_accept_a_maximum_above_machine_words() {
    let mut config = sized_config(0, 11);
    config.max_memories = power(80);
    let cells: [u64; 11] = [0, 1, 0, 0, 0, 1, 1, 281474976710656, 1, 0, 0];
    let tape: Tape = cells.into_iter().rev().fold(Tape::Empty,
        |tail, head| Tape::Cons(head, Box::new(tail)));
    let (module, choices) = match replay(config, tape) {
        Ok(result) => result,
        Err(_) => panic!("recursive memory choices must allow an arbitrary binary maximum"),
    };
    match module.memories {
        Memories::Cons(first, tail) => {
            assert!(matches!(first.address, AddressType::I32));
            assert_eq!(first.minimum, 0);
            assert_eq!(first.maximum, None);
            match *tail {
                Memories::Cons(second, rest) => {
                    assert!(matches!(second.address, AddressType::I64));
                    assert_eq!(second.minimum, 281474976710656);
                    assert_eq!(second.maximum, Some(281474976710656));
                    assert!(matches!(*rest, Memories::Empty));
                }
                _ => panic!("second continuation must construct the second memory"),
            }
        }
        _ => panic!("first continuation must construct the first memory"),
    }
    assert_eq!(value(&choices.remaining), 0);
}

#[test]
fn natural_indices_preserve_compact_word_choices() {
    for (bound, cell) in [(1, 0), (1u64 << 32, 17), (u64::MAX, u64::MAX - 1)] {
        let choices: Choices = Choices {
            source: Source::Replay(Tape::Cons(cell, Box::new(Tape::Empty)), Natural::Zero),
            trace: Tape::Empty, remaining: natural::from_u64(1),
        };
        let (selected, state) = match pick_natural(&natural::from_u64(bound), choices) {
            Ok(result) => result,
            Err(_) => panic!("natural index must preserve compact bound {bound} and cell {cell}"),
        };
        assert_eq!(value(&selected), u128::from(cell));
        assert_eq!(value(&state.remaining), 0);
        match state.source {
            Source::Replay(Tape::Empty, offset) => assert_eq!(value(&offset), 1),
            _ => panic!("compact natural index must consume exactly one cell"),
        }
    }
}

#[test]
fn natural_indices_cross_the_word_boundary_with_exact_state() {
    for (exponent, cells, expected) in [
        (64, vec![1, u64::MAX - 1], u128::from(u64::MAX)),
        (80, vec![1, 1, 0], 2),
    ] {
        let count: u64 = cells.len() as u64;
        let tape: Tape = cells.into_iter().rev().fold(Tape::Cons(77, Box::new(Tape::Empty)),
            |tail, head| Tape::Cons(head, Box::new(tail)));
        let choices: Choices = Choices {
            source: Source::Replay(tape, power(80)),
            trace: Tape::Cons(99, Box::new(Tape::Empty)),
            remaining: natural::from_u64(count + 1),
        };
        let (selected, state) = match pick_natural(&power(exponent), choices) {
            Ok(result) => result,
            Err(_) => panic!("natural index must accept exclusive bound 2^{exponent}"),
        };
        assert_eq!(value(&selected), expected);
        assert_eq!(value(&state.remaining), 1);
        match state.source {
            Source::Replay(Tape::Cons(77, tail), offset) => {
                assert!(matches!(*tail, Tape::Empty));
                assert_eq!(value(&offset), (1u128 << 80) + u128::from(count));
            }
            _ => panic!("unbounded choice must preserve the trailing tape"),
        }
        let mut trace: Vec<u64> = Vec::new();
        let mut rest: Tape = state.trace;
        while let Tape::Cons(head, tail) = rest {
            trace.push(head);
            rest = *tail;
        }
        assert_eq!(trace, if exponent == 64 { vec![u64::MAX - 1, 1, 99] } else { vec![0, 1, 1, 99] });
    }
}

#[test]
fn natural_indices_reject_empty_domains_and_malformed_tapes() {
    let empty: Choices = Choices {
        source: Source::Replay(Tape::Empty, Natural::Zero),
        trace: Tape::Empty, remaining: Natural::Zero,
    };
    assert!(matches!(pick_natural(&Natural::Zero, empty), Err(GenerationError::InternalInvariant)));
    let invalid: Choices = Choices {
        source: Source::Replay(Tape::Cons(2, Box::new(Tape::Empty)), Natural::Zero),
        trace: Tape::Empty, remaining: natural::from_u64(1),
    };
    assert!(matches!(pick_natural(&power(80), invalid), Err(GenerationError::ChoiceOutOfRange(_, 2, 2))));
}

#[test]
fn natural_difference_preserves_borrows_above_machine_words() {
    let high: Natural = power(80);
    let half: Natural = power(79);
    let result: Natural = match natural::difference(&high, &half) {
        Some(result) => result,
        None => panic!("2^80 minus 2^79 must not underflow"),
    };
    assert_eq!(value(&result), 1u128 << 79);
    let boundary: Natural = match natural::difference(&power(64), &natural::from_u64(1)) {
        Some(result) => result,
        None => panic!("2^64 minus one must be representable"),
    };
    assert_eq!(value(&boundary), u128::from(u64::MAX));
    let next: Natural = natural::increment(natural::copy(&high));
    assert!(matches!(natural::difference(&high, &next), None));
    assert!(matches!(natural::difference(&high, &high), Some(Natural::Zero)));
    assert_eq!(value(&high), 1u128 << 80);
}

#[test]
fn recursive_sequence_lookup_does_not_truncate_indices() {
    use generator_rust::wasm::sequence::{self, Sequence};
    let values: Sequence<u64> = sequence::cons(10,
        sequence::cons(20, sequence::cons(30, Sequence::Empty)));
    assert_eq!(sequence::get(&values, natural::from_u64(1)), Some(&20));
    assert_eq!(sequence::get(&values, natural::increment(power(80))), None);
    assert_eq!(value(&sequence::length(&values)), 3);
    assert_eq!(sequence::last(&values), Some(&30));
    let joined: Sequence<u64> = sequence::append(values, sequence::cons(40, Sequence::Empty));
    let (prefix, suffix): (Sequence<u64>, Sequence<u64>) = match
        sequence::split_at(joined, natural::from_u64(2)) {
        Some(parts) => parts,
        None => panic!("a four-element sequence must split at two"),
    };
    assert_eq!(sequence::last(&prefix), Some(&20));
    assert_eq!(sequence::get(&suffix, Natural::Zero), Some(&30));
    let reversed: Sequence<u64> = sequence::reverse(prefix);
    assert_eq!(sequence::get(&reversed, Natural::Zero), Some(&20));
    assert_eq!(sequence::last(&reversed), Some(&10));
}

#[test]
fn natural_choice_selects_from_the_recursive_sequence() {
    use generator_rust::wasm::sequence::{self, Sequence};
    let cells: [u64; 3] = [1, 1, 0];
    let tape: Tape = cells.into_iter().rev().fold(Tape::Empty,
        |tail, head| Tape::Cons(head, Box::new(tail)));
    let choices: Choices = Choices { source: Source::Replay(tape, Natural::Zero),
        trace: Tape::Empty, remaining: natural::from_u64(3) };
    let (index, final_state): (Natural, Choices) = match pick_natural(&power(80), choices) {
        Ok(result) => result,
        Err(_) => panic!("the wide bound must select index two"),
    };
    let values: Sequence<u64> = sequence::cons(10,
        sequence::cons(20, sequence::cons(30, Sequence::Empty)));
    assert_eq!(sequence::select(values, index), Some(30));
    assert_eq!(value(&final_state.remaining), 0);
}

#[test]
fn full_replay_accepts_all_numeric_bounds_above_machine_words() {
    use generator_rust::wasm::sequence::Sequence;
    let mut config = sized_config(0, 1);
    config.max_types = power(80);
    config.max_functions = power(80);
    config.max_parameters = power(80);
    config.max_results = power(80);
    config.max_locals = power(80);
    config.max_exports = power(80);
    config.fuel = power(80);
    let (module, choices) = match replay(config, Tape::Cons(0, Box::new(Tape::Empty))) {
        Ok(result) => result,
        Err(_) => panic!("an empty module must replay with all numeric bounds above u64"),
    };
    assert!(matches!(module.types, Sequence::Empty));
    assert!(matches!(module.functions, Sequence::Empty));
    assert!(matches!(module.exports, Sequence::Empty));
    assert_eq!(value(&choices.remaining), 0);
}

#[test]
fn unbounded_bounds_preserve_signatures_indices_and_decimal_export_names() {
    use generator_rust::wasm::sequence::{self, Sequence};
    use generator_rust::wasm::{Instruction, ValueType};
    let mut config = sized_config(0, 1000);
    config.max_types = power(80);
    config.max_functions = power(80);
    config.max_parameters = power(80);
    config.max_results = power(80);
    config.max_locals = power(80);
    config.max_exports = power(80);
    config.fuel = power(80);
    let mut cells: Vec<u64> = vec![1,0, 1,0, 0,0, 1,1,0, 0,1, 1,0, 0, 1,0, 0];
    cells.extend([1; 12]);
    cells.push(0);
    cells.extend([0; 12]);
    cells.extend([1,0, 0, 0,1, 0]);
    let consumed: u128 = cells.len() as u128;
    let tape: Tape = cells.into_iter().rev().fold(Tape::Empty,
        |tail, head| Tape::Cons(head, Box::new(tail)));
    let (module, choices) = match replay(config, tape) {
        Ok(result) => result,
        Err(_) => panic!("wide bounds must preserve actual function and export construction"),
    };
    let group = match sequence::get(&module.types, Natural::Zero) {
        Some(value) => value,
        None => panic!("one type must be generated"),
    };
    let signature = &sequence::get(&group.members, Natural::Zero).expect("one group member").signature;
    assert_eq!(value(&sequence::length(&signature.parameters)), 2);
    assert!(matches!(sequence::get(&signature.parameters, Natural::Zero), Some(ValueType::I32)));
    assert!(matches!(sequence::get(&signature.parameters, natural::from_u64(1)), Some(ValueType::I64)));
    let function = match sequence::get(&module.functions, Natural::Zero) {
        Some(value) => value,
        None => panic!("one function must be generated"),
    };
    assert_eq!(value(&function.type_index), 0);
    match &function.body {
        Sequence::Cons(cell) => {
            match &cell.0 {
                Instruction::LocalGet(index) => assert_eq!(value(index), 0),
                _ => panic!("the body must contain the chosen local.get"),
            }
            assert!(matches!(cell.1, Sequence::Empty));
        }
        _ => panic!("the body must contain exactly one instruction"),
    }
    assert_eq!(value(&sequence::length(&module.exports)), 12);
    for (index, expected) in [(9, b"e9".as_slice()), (10, b"e10".as_slice()), (11, b"e11".as_slice())] {
        let export = match sequence::get(&module.exports, natural::from_u64(index)) {
            Some(value) => value,
            None => panic!("export index {index} must exist"),
        };
        let mut name: Vec<u8> = Vec::new();
        let mut rest = &export.name;
        while let Sequence::Cons(cell) = rest { name.push(cell.0); rest = &cell.1; }
        assert_eq!(name, expected);
        assert_eq!(value(&export.function_index), 0);
    }
    assert_eq!(value(&choices.remaining), 1000 - consumed - 1);
}
