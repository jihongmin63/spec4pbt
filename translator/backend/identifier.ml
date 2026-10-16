(* Identifier-shaped reserved tokens from Lean 4.34.1, the pinned toolchain.
   Enumerated with (Lean.Parser.getTokenTable env).values after importing Lean;
   the lexer recognizes these tokens before ordinary unquoted identifiers.
   Keep the legacy true/false exclusions as well. *)
let lean_keywords : string list =
  [
    "Prop"; "Sort"; "StateRefT"; "Type"; "_"; "abbrev"; "add_decl_doc"; "assert!";
    "assert_not_exists"; "assert_not_imported"; "at"; "attribute"; "aux_def"; "axiom";
    "bif"; "binder_predicate"; "break"; "builtin_cbv_simproc";
    "builtin_cbv_simproc_decl"; "builtin_dsimproc"; "builtin_dsimproc_decl";
    "builtin_grind_propagator"; "builtin_initialize"; "builtin_simproc";
    "builtin_simproc_decl"; "by"; "by?"; "by_elab"; "calc"; "catch"; "cbv_eval";
    "cbv_simproc"; "cbv_simproc_decl"; "class"; "coinductive"; "coinductive_fixpoint";
    "continue"; "dbg_trace"; "debug_assert!"; "declare_bitwise_int_theorems";
    "declare_bitwise_uint_theorems"; "declare_command_config_elab";
    "declare_command_config_elab_legacy"; "declare_config_elab";
    "declare_config_elab_legacy"; "declare_core_config_elab"; "declare_eval_bin";
    "declare_eval_bin_bitwise"; "declare_eval_bin_bool_pred"; "declare_int_theorems";
    "declare_simp_like_tactic"; "declare_sint_simprocs"; "declare_syntax_cat";
    "declare_term_config_elab"; "declare_uint_simprocs"; "declare_uint_theorems";
    "decreasing_by"; "def"; "def_eval_config_item"; "deprecated_module";
    "deprecated_syntax"; "deriving"; "do"; "docs_to_verso"; "dsimproc"; "dsimproc_decl";
    "elab"; "elab_rules"; "elab_stx_quot"; "else"; "end"; "eval_prec"; "eval_prio";
    "example"; "exists"; "export"; "extends"; "f!"; "false"; "finally"; "for"; "forall";
    "from"; "fun"; "generalizing"; "grind_annotated"; "grind_pattern";
    "grind_propagator"; "have"; "haveI"; "hiding"; "idbg"; "if"; "import"; "in";
    "include"; "include_str"; "inductive"; "inductive_fixpoint"; "inferInstanceAs";
    "infix"; "infixl"; "infixr"; "init_grind_norm"; "init_quot"; "initialize";
    "instance"; "leading_parser"; "let"; "letI"; "let_delayed"; "let_expr"; "let_fun";
    "let_tmp"; "local"; "logNamedError"; "logNamedErrorAt"; "logNamedWarning";
    "logNamedWarningAt"; "m!"; "macro"; "macro_rules"; "match"; "match_expr"; "matches";
    "max_prec"; "meta"; "mod_cast"; "mut"; "mutual"; "namespace"; "nat_lit"; "no_index";
    "nofun"; "nomatch"; "noncomputable"; "nonrec"; "norm_cast_add_elim"; "notation";
    "omit"; "opaque"; "open"; "panic!"; "partial"; "partial_fixpoint"; "postfix";
    "prefix"; "println!"; "private"; "protected"; "public"; "recommended_spelling";
    "register_builtin_option"; "register_error_explanation"; "register_grind_attr";
    "register_label_attr"; "register_linter_set"; "register_option";
    "register_parser_alias"; "register_simp_attr"; "register_sym_dsimp";
    "register_sym_simp"; "register_sym_simp_attr"; "register_tactic_tag";
    "register_try?_tactic"; "renaming"; "repeat"; "reportDbgIssue!";
    "reportEMatchIssue!"; "reportIssue!"; "reprove"; "return"; "run_cmd"; "run_elab";
    "run_meta"; "s!"; "scoped"; "seal"; "section"; "set_library_suggestions";
    "set_option"; "show"; "show_panel_widgets"; "show_term"; "show_term_elab";
    "simproc"; "simproc_decl"; "sorry"; "structure"; "suffices"; "syntax"; "tactic_alt";
    "tactic_extension"; "tactic_name"; "tactic_tag"; "termination_by";
    "termination_by?"; "test_extern"; "then"; "theorem"; "throwError"; "throwErrorAt";
    "throwNamedError"; "throwNamedErrorAt"; "trailing_parser"; "true"; "try";
    "unif_hint"; "universe"; "unless"; "unlock_limits"; "unreachable!"; "unsafe";
    "unseal"; "until"; "using"; "using!"; "variable"; "where"; "while"; "with";
    "with_annotate_term"; "with_weak_namespace"; "without_expected_type"
  ]

let is_letter (character : char) : bool =
  (character >= 'a' && character <= 'z')
  || (character >= 'A' && character <= 'Z')

let is_digit (character : char) : bool =
  character >= '0' && character <= '9'

let contains_closing_quote (name : string) : bool =
  let rec search (index : int) : bool =
    index + 1 < String.length name
    &&
    ((name.[index] = '\194' && name.[index + 1] = '\187')
    || search (index + 1))
  in
  search 0

let name_of_var (id : Lang.Il.id) (iters : Lang.Il.iter list) : string =
  id.it ^ String.concat "" (List.map Lang.Il.Print.string_of_iter iters)

let print_identifier (name : string) : string =
  if contains_closing_quote name then
    invalid_arg ("Lean identifier contains closing quote: " ^ name);
  let valid_start : bool =
    String.length name > 0 && (is_letter name.[0] || name.[0] = '_')
  in
  let valid_rest : bool =
    String.for_all
      (fun character ->
        is_letter character || is_digit character
        || List.mem character [ '_'; '\''; '!'; '?' ])
      name
  in
  if valid_start && valid_rest && name <> "_" && not (List.mem name lean_keywords)
  then name
  else "«" ^ name ^ "»"
