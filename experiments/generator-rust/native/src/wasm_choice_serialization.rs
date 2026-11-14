use generator_rust::wasm::choices::Tape;
use generator_rust::wasm::natural::{Natural, Positive};

fn decimal_bit(decimal: &str, bit: u8) -> String {
    let mut carry: u8 = bit;
    let mut digits: Vec<char> = Vec::new();
    for digit in decimal.bytes().rev() {
        let value: u8 = 2 * (digit - b'0') + carry;
        digits.push(char::from(b'0' + value % 10));
        carry = value / 10;
    }
    if carry != 0 {
        digits.push(char::from(b'0' + carry));
    }
    digits.into_iter().rev().collect()
}

fn positive_decimal(value: &Positive) -> String {
    match value {
        Positive::One => "1".to_owned(),
        Positive::Bit0(tail) => decimal_bit(&positive_decimal(tail), 0),
        Positive::Bit1(tail) => decimal_bit(&positive_decimal(tail), 1),
    }
}

pub fn natural_decimal(value: &Natural) -> String {
    match value {
        Natural::Zero => "0".to_owned(),
        Natural::Positive(value) => positive_decimal(value),
    }
}

pub fn tape_from_cells(cells: Vec<u64>) -> Tape {
    cells.into_iter().rev().fold(Tape::Empty, |tail, head| Tape::Cons(head, Box::new(tail)))
}

pub fn trace_json(trace: &Tape) -> String {
    let mut cells: Vec<String> = Vec::new();
    let mut rest: &Tape = trace;
    while let Tape::Cons(value, tail) = rest {
        cells.push(value.to_string());
        rest = tail;
    }
    cells.reverse();
    format!("[{}]", cells.join(","))
}
