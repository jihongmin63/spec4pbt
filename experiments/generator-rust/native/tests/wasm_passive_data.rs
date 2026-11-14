use generator_rust::wasm::{replay, sized_config};

#[path = "../src/wasm_choice_serialization.rs"]
mod wasm_choice_serialization;
#[path = "../src/wasm_serialization.rs"]
mod wasm_serialization;

fn passive_report(payloads: &[&str]) -> String {
    let mut cells: Vec<u64> = vec![0];
    if !payloads.is_empty() {
        cells.extend([0, 0]);
    }
    for payload in payloads {
        cells.push(1);
        for character in payload.chars() {
            let point: u64 = character as u64;
            cells.extend([1, if point < 0xd800 { point } else { point - 0x800 }]);
        }
        cells.push(0);
    }
    let config = sized_config(payloads.len(), cells.len() as u64);
    let tape = wasm_choice_serialization::tape_from_cells(cells);
    let (module, _) = match replay(config, tape) {
        Ok(output) => output,
        Err(error) => panic!("passive data replay failed: {}", wasm_serialization::error_message(error)),
    };
    wasm_serialization::module_json(&module)
}

#[test]
fn full_replay_preserves_passive_unicode_payloads() {
    let output: String = passive_report(&["", "\0\n\"\\", "한글🦀", "e\u{301}", "\u{d7ff}\u{e000}\u{10ffff}"]);
    let expected: &str = "\"DATAS\":[{\"DINIT\":\"\",\"DMODE\":\"Passive\"},{\"DINIT\":\"\\u0000\\u000a\\\"\\\\\",\"DMODE\":\"Passive\"},{\"DINIT\":\"한글🦀\",\"DMODE\":\"Passive\"},{\"DINIT\":\"e\u{301}\",\"DMODE\":\"Passive\"},{\"DINIT\":\"\u{d7ff}\u{e000}\u{10ffff}\",\"DMODE\":\"Passive\"}]";
    assert!(output.contains(expected), "payloads changed: {output}");
}

#[test]
fn data_section_exceeds_frontend_sample_size() {
    let payloads: Vec<&str> = vec![""; 129];
    let output: String = passive_report(&payloads);
    assert_eq!(output.matches("\"DMODE\":\"Passive\"").count(), payloads.len());
}
