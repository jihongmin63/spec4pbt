import properties.wasm_module_ok.ConstructiveBodyControlProductions
import properties.wasm_module_ok.ConstructiveBodyCatchLists
import properties.wasm_module_ok.ConstructiveBodyEvalReduction
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyControlOriginal
open SpecTec properties.wasm_module_ok SpecTecExecution ConstructiveBodyEnvironment ConstructiveBodyBlocktypes ConstructiveBodyEvalReduction

theorem block (c : context) (stack : inferresulttype) (bt : blocktype) (body : List instr)
    (effect : inferinstrtype) (n finish : Nat)
    (h : Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.BLOCK bt body)⟩)
      n (.success (.of effect)) finish) :
    ∃sig∈signatures c,sig.raw=bt ∧
      Eval SpecTec.specTecProgram (.call ⟨Unit,SpecTecCall.Block_ok {c with LABELS:=sig.outputs::c.LABELS}
        (.InstrT sig.inputs sig.outputs []) body⟩) n (.success (.of ())) finish ∧
      effect=ConstructiveBodyControl.effect sig.inputs sig.outputs := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.BLOCK bt body) 5 (by decide) rfl (by decide) effect n finish).1 h
  change Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:5» c stack (.BLOCK bt body)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:5» at hs
  obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
  cases hs with | bind_success ht tail =>
    rename_i middle ty
    obtain ⟨sig,hmem,hraw,hty,hn⟩ := ConstructiveBodyBlocktypeCoverage.signatures_complete c bt ty n middle ht
    subst middle
    rw [hty] at tail
    cases tail with | bind_success hb hp =>
      cases hp
      exact ⟨sig,hmem,hraw,hb,rfl⟩

theorem loop (c : context) (stack : inferresulttype) (bt : blocktype) (body : List instr)
    (effect : inferinstrtype) (n finish : Nat)
    (h : Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.LOOP bt body)⟩)
      n (.success (.of effect)) finish) :
    ∃sig∈signatures c,sig.raw=bt ∧
      Eval SpecTec.specTecProgram (.call ⟨Unit,SpecTecCall.Block_ok {c with LABELS:=sig.inputs::c.LABELS}
        (.InstrT sig.inputs sig.outputs []) body⟩) n (.success (.of ())) finish ∧
      effect=ConstructiveBodyControl.effect sig.inputs sig.outputs := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.LOOP bt body) 6 (by decide) rfl (by decide) effect n finish).1 h
  change Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:6» c stack (.LOOP bt body)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:6» at hs
  obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
  cases hs with | bind_success ht tail =>
    rename_i middle ty
    obtain ⟨sig,hmem,hraw,hty,hn⟩ := ConstructiveBodyBlocktypeCoverage.signatures_complete c bt ty n middle ht
    subst middle
    rw [hty] at tail
    cases tail with | bind_success hb hp =>
      cases hp
      exact ⟨sig,hmem,hraw,hb,rfl⟩

theorem ifElse (c : context) (stack : inferresulttype) (bt : blocktype) (yes no : List instr)
    (effect : inferinstrtype) (n finish : Nat)
    (h : Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«IF % % ELSE %» bt yes no)⟩)
      n (.success (.of effect)) finish) :
    ∃sig∈signatures c,∃middle,sig.raw=bt ∧
      Eval SpecTec.specTecProgram (.call ⟨Unit,SpecTecCall.Block_ok {c with LABELS:=sig.outputs::c.LABELS}
        (.InstrT sig.inputs sig.outputs []) yes⟩) n (.success (.of ())) middle ∧
      Eval SpecTec.specTecProgram (.call ⟨Unit,SpecTecCall.Block_ok {c with LABELS:=sig.outputs::c.LABELS}
        (.InstrT sig.inputs sig.outputs []) no⟩) middle (.success (.of ())) finish ∧
      effect=ConstructiveBodyControl.effect (sig.inputs++[.NumT .I32T]) sig.outputs := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.«IF % % ELSE %» bt yes no) 7 (by decide) rfl (by decide) effect n finish).1 h
  change Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:7» c stack (.«IF % % ELSE %» bt yes no)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:7» at hs
  obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
  cases hs with | bind_success ht tail =>
    rename_i middle ty
    obtain ⟨sig,hmem,hraw,hty,hn⟩ := ConstructiveBodyBlocktypeCoverage.signatures_complete c bt ty n middle ht
    subst middle
    rw [hty] at tail
    cases tail with | bind_success hy tail =>
      cases tail with | bind_success hn hp =>
        cases hp
        exact ⟨sig,hmem,_,hraw,hy,hn,rfl⟩

theorem tryTable (c : context) (stack : inferresulttype) (env : Env c) (bt : blocktype)
    (handlers : List SpecTec.«catch») (body : List instr) (effect : inferinstrtype) (n finish : Nat)
    (h : Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.TRY_TABLE bt handlers body)⟩)
      n (.success (.of effect)) finish) :
    ∃sig∈signatures c,sig.raw=bt ∧
      (∀x∈handlers,ConstructiveBodyCatchCoverage.Covers c env x) ∧
      Eval SpecTec.specTecProgram (.call ⟨Unit,SpecTecCall.Block_ok {c with LABELS:=sig.outputs::c.LABELS}
        (.InstrT sig.inputs sig.outputs []) body⟩) n (.success (.of ())) finish ∧
      effect=ConstructiveBodyControl.effect sig.inputs sig.outputs := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.TRY_TABLE bt handlers body) 24 (by decide) rfl (by decide) effect n finish).1 h
  change Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:24» c stack (.TRY_TABLE bt handlers body)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:24» at hs
  obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
  cases hs with | bind_success ht tail =>
    rename_i middle ty
    obtain ⟨sig,hmem,hraw,hty,hn⟩ := ConstructiveBodyBlocktypeCoverage.signatures_complete c bt ty n middle ht
    subst middle
    rw [hty] at tail
    cases tail with | bind_success hh tail =>
      rename_i middle value
      cases value
      obtain ⟨hc,hn⟩ := ConstructiveBodyCatchLists.iter_covered c env sig.outputs handlers n middle hh
      subst middle
      cases tail with | bind_success hb hp =>
        cases hp
        exact ⟨sig,hmem,hraw,hc,hb,rfl⟩

#print axioms block
#print axioms ifElse
#print axioms tryTable
end properties.wasm_module_ok.ConstructiveBodyControlOriginal
