use generator_rust::wasm::{natural, replay, sized_config};

#[path = "../src/wasm_choice_serialization.rs"]
mod wasm_choice_serialization;
#[path = "../src/wasm_serialization.rs"]
mod wasm_serialization;

fn power_cells(exponent: usize) -> Vec<u64> {
    let mut cells: Vec<u64> = vec![4294967296];
    cells.extend(vec![1; exponent]);
    cells.push(0);
    cells
}

fn import_report(count: u64, cells: Vec<u64>) -> String {
    let mut config = sized_config(0, cells.len() as u64);
    config.max_memory_imports = natural::from_u64(count);
    let tape = wasm_choice_serialization::tape_from_cells(cells);
    let (module, _) = match replay(config, tape) {
        Ok(output) => output,
        Err(error) => panic!("memory import replay failed: {}", wasm_serialization::error_message(error)),
    };
    wasm_serialization::module_json(&module)
}

#[test]
fn full_replay_preserves_unbounded_names_and_original_memory_limits() {
    let mut module_name: Vec<u64> = vec![1, 0, 1];
    module_name.extend(power_cells(80));
    module_name.extend([1, 55296, 0]);
    let mut item_name: Vec<u64> = vec![1, 1114112, 1];
    item_name.extend(power_cells(64));
    item_name.push(0);
    let mut cells: Vec<u64> = vec![0, 1, 0, 65536, 1, 0];
    cells.extend_from_slice(&module_name);
    cells.extend_from_slice(&item_name);
    cells.extend([1, 1, 281474976710656, 0]);
    cells.extend_from_slice(&module_name);
    cells.extend_from_slice(&item_name);
    let output: String = import_report(2, cells);
    let first: &str = "{\"MODULENAME\":[0,1208925819614629174706176,55296],\"ITEMNAME\":[1114112,18446744073709551616],\"IDESC\":{\"MemImport\":{\"MemoryT\":[\"I32AT\",{\"MIN\":65536,\"MAX\":65536}]}}}";
    let second: &str = "{\"MODULENAME\":[0,1208925819614629174706176,55296],\"ITEMNAME\":[1114112,18446744073709551616],\"IDESC\":{\"MemImport\":{\"MemoryT\":[\"I64AT\",{\"MIN\":281474976710656,\"MAX\":null}]}}}";
    assert!(output.contains(&format!("\"IMPORTS\":[{first},{second}]")), "imports changed: {output}");
    assert!(output.contains("\"MEMS\":[]"), "imports moved into definitions: {output}");
}

#[test]
fn import_section_exceeds_frontend_sample_size() {
    let mut cells: Vec<u64> = vec![0];
    for _ in 0..129 {
        cells.extend([1, 0, 0, 0, 0, 0]);
    }
    let output: String = import_report(129, cells);
    assert_eq!(output.matches("\"MemImport\"").count(), 129);
    assert_eq!(output.matches("\"MODULENAME\":[],\"ITEMNAME\":[]").count(), 129);
}
