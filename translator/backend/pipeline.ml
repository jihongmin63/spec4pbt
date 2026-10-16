(** Backend entrypoint for normalized compatibility IL.
    Current_adapter owns conversion from the pinned upstream IL, including
    directional bindings, input modes and fallback order. The backend never
    invokes the donor parser, elaborator, AL passes or P4 frontend. *)
module S = Ast.SpecTec

let ( let* ) = Result.bind

let transpile ?(namespace = "SpecTec") ?(ordered = true) ?(executable = false) (input : S.spec) :
    (string, Diagnostic.t) result =
  Printer.global_namespace := namespace;
  if ordered then Execution_translate.transpile ~executable input else
  let* lean_ast = Translator.translate input in
  let* ordered = Order.order lean_ast in
  Ok (Printer.print ordered)

let transpile_all ?(namespace = "SpecTec") ?(ordered = true) ?(executable = false) (input : S.spec) : string * Diagnostic.t list =
  Printer.global_namespace := namespace;
  if ordered then Execution_translate.transpile_all ~executable input else
  let (lean_ast, diagnostics) :
      Ast.Lean.located_declaration list * Diagnostic.t list =
    Translator.translate_all input
  in
  let (ordered, ordering_diagnostics) :
      Ast.Lean.program * Diagnostic.t list = Order.order_all lean_ast
  in
  (Printer.print ordered, diagnostics @ ordering_diagnostics)
