use generator_rust::wasm::{Config, replay, sized_config};
use generator_rust::wasm::natural;

#[path = "../src/wasm_choice_serialization.rs"]
mod wasm_choice_serialization;
#[path = "../src/wasm_serialization.rs"]
mod wasm_serialization;

fn replay_module(config: Config, cells: Vec<u64>) -> String {
    let tape = wasm_choice_serialization::tape_from_cells(cells);
    let (module, _) = match replay(config, tape) {
        Ok(output) => output,
        Err(error) => panic!("type-context replay failed: {}", wasm_serialization::error_message(error)),
    };
    wasm_serialization::module_json(&module)
}

fn expected_module(types: &str, functions: &str, exports: &str) -> String {
    format!("{{\"TYPES\":[{types}],\"GLOBALS\":[],\"TABLES\":[],\"MEMS\":[],\"TAGS\":[],\"FUNCS\":[{functions}],\"START\":null,\"ELEMS\":[],\"DATAS\":[],\"IMPORTS\":[],\"EXPORTS\":[{exports}]}}")
}

#[test]
fn recursive_group_preserves_raw_parent_and_recursive_parameter() {
    let mut config: Config = sized_config(0, 100);
    config.max_types = natural::from_u64(2);
    config.max_parameters = natural::from_u64(1);
    let output: String = replay_module(config, vec![1, 2, 1, 0, 0, 1, 1, 2, 0, 0, 0, 0]);
    let types: &str = r#"{"RecT":[{"SubT":["NoFinal",[],{"DefFuncT":{"FuncT":[[{"RefT":{"% %":["Null",{"VarHT":{"StatX":0}}]}}],[]]}}]},{"SubT":["Final",[{"VarHT":{"StatX":0}}],{"DefFuncT":{"FuncT":[[{"RefT":{"% %":["Null",{"VarHT":{"StatX":0}}]}}],[]]}}]}]}"#;
    assert_eq!(output, expected_module(types, "", ""));
}

#[test]
fn recursive_group_preserves_forward_and_backward_references() {
    let mut config: Config = sized_config(0, 100);
    config.max_types = natural::from_u64(2);
    config.max_parameters = natural::from_u64(1);
    let output: String = replay_module(config, vec![1, 2, 0, 0, 0, 0, 1, 2, 0, 1, 0, 1, 2, 0, 0, 0, 0]);
    let types: &str = r#"{"RecT":[{"SubT":["Final",[],{"DefFuncT":{"FuncT":[[{"RefT":{"% %":["Null",{"VarHT":{"StatX":1}}]}}],[]]}}]},{"SubT":["Final",[],{"DefFuncT":{"FuncT":[[{"RefT":{"% %":["Null",{"VarHT":{"StatX":0}}]}}],[]]}}]}]}"#;
    assert_eq!(output, expected_module(types, "", ""));
}

#[test]
fn body_matches_closed_aliases_without_rewriting_raw_indices() {
    let mut config: Config = sized_config(0, 100);
    config.max_types = natural::from_u64(3);
    config.max_functions = natural::from_u64(1);
    config.max_parameters = natural::from_u64(1);
    config.max_results = natural::from_u64(1);
    let output: String = replay_module(config, vec![3, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0,
        1, 0, 0, 1, 2, 0, 0, 1, 2, 0, 1, 1, 2, 0, 0, 1, 0]);
    let types: &str = r#"{"RecT":[{"SubT":["Final",[],{"DefFuncT":{"FuncT":[[],[]]}}]}]},{"RecT":[{"SubT":["Final",[],{"DefFuncT":{"FuncT":[[],[]]}}]}]},{"RecT":[{"SubT":["Final",[],{"DefFuncT":{"FuncT":[[{"RefT":{"% %":["Null",{"VarHT":{"StatX":0}}]}}],[{"RefT":{"% %":["Null",{"VarHT":{"StatX":1}}]}}]]}}]}]}"#;
    let functions: &str = r#"{"FTYPE":2,"LOCALS":[],"BODY":[{"LOCAL.GET":0}]}"#;
    assert_eq!(output, expected_module(types, functions, ""));
}

#[test]
fn export_declares_reference_before_body_generation() {
    let mut config: Config = sized_config(0, 100);
    config.max_types = natural::from_u64(1);
    config.max_functions = natural::from_u64(1);
    config.max_exports = natural::from_u64(1);
    config.fuel = natural::from_u64(1);
    let output: String = replay_module(config, vec![1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 15, 0, 0]);
    let types: &str = r#"{"RecT":[{"SubT":["Final",[],{"DefFuncT":{"FuncT":[[],[]]}}]}]}"#;
    let functions: &str = r#"{"FTYPE":0,"LOCALS":[],"BODY":[{"REF.FUNC":0},"DROP"]}"#;
    let exports: &str = r#"{"NAME":[101,48],"EDESC":{"FuncExport":0}}"#;
    assert_eq!(output, expected_module(types, functions, exports));
}

#[test]
fn reference_authorization_uses_function_indices_independently_of_type_aliases() {
    let mut config: Config = sized_config(0, 21);
    config.max_types = natural::from_u64(1);
    config.max_functions = natural::from_u64(2);
    config.max_exports = natural::from_u64(1);
    config.fuel = natural::from_u64(1);
    let output: String = replay_module(config, vec![1, 1, 0, 0, 0, 0, 2, 0, 0, 1, 1, 0, 16, 0, 0, 0, 0]);
    let types: &str = r#"{"RecT":[{"SubT":["Final",[],{"DefFuncT":{"FuncT":[[],[]]}}]}]}"#;
    let functions: &str = r#"{"FTYPE":0,"LOCALS":[],"BODY":[{"REF.FUNC":1},"DROP"]},{"FTYPE":0,"LOCALS":[],"BODY":[]}"#;
    let exports: &str = r#"{"NAME":[101,48],"EDESC":{"FuncExport":1}}"#;
    assert_eq!(output, expected_module(types, functions, exports));
}
