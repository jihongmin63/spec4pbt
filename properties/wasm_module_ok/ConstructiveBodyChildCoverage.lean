import properties.wasm_module_ok.ConstructiveBodyControlOriginal
import properties.wasm_module_ok.ConstructiveBodyFunctionCoverage
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyChildCoverage
open SpecTec properties.wasm_module_ok SpecTecExecution ConstructiveBodyEnvironment ConstructiveBodyBlocktypes ConstructiveBodyControlProductions ConstructiveBodyProductions ConstructiveBodyProductionCoverage

/-- Proof-only induction interface for strictly smaller original bodies. -/
def Complete (child : Builder) (parent : instr) : Prop :=
  ∀(c : context) (env : Env c) (ins outs : List valtype)
    (hi : ∀t∈ins,CandidateValMatch.InTableVal c t) (ho : ∀t∈outs,CandidateValMatch.InTableVal c t)
    (code : List instr) (n finish : Nat),sizeOf code<sizeOf parent →
    Eval SpecTec.Body (.call ⟨Unit,Call.Block_ok c (.InstrT ins outs []) code⟩)
      n (.success (.of ())) finish →
    ∃b,Gen.support (child c env ins outs hi ho).generator b ∧ b.val=code

theorem signature_inputs (c : context) (env : Env c) (sig : Signature c) :
    ∀t∈sig.inputs,CandidateValMatch.InTableVal c t := fun t ht =>
  ConstructiveBodyBlocktypeCoverage.signature_backed c env sig t (List.mem_append_left _ ht)
theorem signature_outputs (c : context) (env : Env c) (sig : Signature c) :
    ∀t∈sig.outputs,CandidateValMatch.InTableVal c t := fun t ht =>
  ConstructiveBodyBlocktypeCoverage.signature_backed c env sig t (List.mem_append_right _ ht)

theorem block (c : context) (stack : inferresulttype) (env : Env c) (child : Builder)
    (bt : blocktype) (code : List instr) (hc : Complete child (.BLOCK bt code))
    (effect : inferinstrtype) (n finish : Nat)
    (h : Eval SpecTec.Body (.call ⟨inferinstrtype,Call.Instr_ok c stack (.BLOCK bt code)⟩)
      n (.success (.of effect)) finish) : Covers (controls c stack env child) (.BLOCK bt code) effect ∧ finish=n := by
  obtain ⟨sig,hmem,hraw,hbody,_⟩ := ConstructiveBodyControlOriginal.block c stack bt code effect n finish h
  let ci := signature_inputs c env sig
  let co := signature_outputs c env sig
  let d : context := {c with LABELS:=sig.outputs::c.LABELS}
  let ed : Env d := env.pushLabel sig.outputs co
  let hi : ∀t∈sig.inputs,CandidateValMatch.InTableVal d t := fun t ht =>
    CandidateProvenanceSteps.in_table_val_of_types_eq c d t rfl (ci t ht)
  let ho : ∀t∈sig.outputs,CandidateValMatch.InTableVal d t := fun t ht =>
    CandidateProvenanceSteps.in_table_val_of_types_eq c d t rfl (co t ht)
  obtain ⟨b,hb,he⟩ := hc d ed sig.inputs sig.outputs hi ho code n finish (by simp +arith) hbody
  have realizes : ∃p∈controls c stack env child,Produces p (.BLOCK bt code) := by
    unfold controls
    refine ⟨?p,?mem,?prod⟩
    case mem =>
      apply List.mem_flatMap.mpr
      refine ⟨sig,hmem,?_⟩
      exact List.mem_cons_self
    case prod =>
      refine ⟨_,⟨b,hb,rfl⟩,?_⟩
      simp only [hraw,he]
  obtain ⟨p,hp,hi⟩ := realizes
  exact ConstructiveBodyFunctionCoverage.from_production c stack (controls c stack env child) p _ effect n finish hp hi h

theorem loop (c : context) (stack : inferresulttype) (env : Env c) (child : Builder)
    (bt : blocktype) (code : List instr) (hc : Complete child (.LOOP bt code))
    (effect : inferinstrtype) (n finish : Nat)
    (h : Eval SpecTec.Body (.call ⟨inferinstrtype,Call.Instr_ok c stack (.LOOP bt code)⟩)
      n (.success (.of effect)) finish) : Covers (controls c stack env child) (.LOOP bt code) effect ∧ finish=n := by
  obtain ⟨sig,hmem,hraw,hbody,_⟩ := ConstructiveBodyControlOriginal.loop c stack bt code effect n finish h
  let ci := signature_inputs c env sig
  let co := signature_outputs c env sig
  let d : context := {c with LABELS:=sig.inputs::c.LABELS}
  let ed : Env d := env.pushLabel sig.inputs ci
  let hi : ∀t∈sig.inputs,CandidateValMatch.InTableVal d t := fun t ht =>
    CandidateProvenanceSteps.in_table_val_of_types_eq c d t rfl (ci t ht)
  let ho : ∀t∈sig.outputs,CandidateValMatch.InTableVal d t := fun t ht =>
    CandidateProvenanceSteps.in_table_val_of_types_eq c d t rfl (co t ht)
  obtain ⟨b,hb,he⟩ := hc d ed sig.inputs sig.outputs hi ho code n finish (by simp +arith) hbody
  have realizes : ∃p∈controls c stack env child,Produces p (.LOOP bt code) := by
    unfold controls
    refine ⟨?p,?mem,?prod⟩
    case mem =>
      apply List.mem_flatMap.mpr
      refine ⟨sig,hmem,?_⟩
      apply List.mem_cons_of_mem
      exact List.mem_cons_self
    case prod =>
      refine ⟨_,⟨b,hb,rfl⟩,?_⟩
      simp only [hraw,he]
  obtain ⟨p,hp,hi⟩ := realizes
  exact ConstructiveBodyFunctionCoverage.from_production c stack (controls c stack env child) p _ effect n finish hp hi h

theorem ifElse (c : context) (stack : inferresulttype) (env : Env c) (child : Builder)
    (bt : blocktype) (yes no : List instr) (hc : Complete child (.«IF % % ELSE %» bt yes no))
    (effect : inferinstrtype) (n finish : Nat)
    (h : Eval SpecTec.Body (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«IF % % ELSE %» bt yes no)⟩)
      n (.success (.of effect)) finish) : Covers (controls c stack env child) (.«IF % % ELSE %» bt yes no) effect ∧ finish=n := by
  obtain ⟨sig,hmem,middle,hraw,hyes,hno,_⟩ := ConstructiveBodyControlOriginal.ifElse c stack bt yes no effect n finish h
  let ci := signature_inputs c env sig
  let co := signature_outputs c env sig
  let d : context := {c with LABELS:=sig.outputs::c.LABELS}
  let ed : Env d := env.pushLabel sig.outputs co
  let hi : ∀t∈sig.inputs,CandidateValMatch.InTableVal d t := fun t ht =>
    CandidateProvenanceSteps.in_table_val_of_types_eq c d t rfl (ci t ht)
  let ho : ∀t∈sig.outputs,CandidateValMatch.InTableVal d t := fun t ht =>
    CandidateProvenanceSteps.in_table_val_of_types_eq c d t rfl (co t ht)
  obtain ⟨byes,hy,hey⟩ := hc d ed sig.inputs sig.outputs hi ho yes n middle (by simp +arith) hyes
  obtain ⟨bno,hn,hen⟩ := hc d ed sig.inputs sig.outputs hi ho no middle finish (by simp +arith) hno
  have realizes : ∃p∈controls c stack env child,Produces p (.«IF % % ELSE %» bt yes no) := by
    unfold controls
    refine ⟨?p,?mem,?prod⟩
    case mem =>
      apply List.mem_flatMap.mpr
      refine ⟨sig,hmem,?_⟩
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      exact List.mem_cons_self
    case prod =>
      refine ⟨_,⟨byes,hy,bno,hn,rfl⟩,?_⟩
      simp only [hraw,hey,hen]
  obtain ⟨p,hp,hi⟩ := realizes
  exact ConstructiveBodyFunctionCoverage.from_production c stack (controls c stack env child) p _ effect n finish hp hi h

theorem tryTable (c : context) (stack : inferresulttype) (env : Env c) (child : Builder)
    (bt : blocktype) (handlers : List SpecTec.«catch») (code : List instr) (hc : Complete child (.«TRY_TABLE» bt handlers code))
    (effect : inferinstrtype) (n finish : Nat)
    (h : Eval SpecTec.Body (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«TRY_TABLE» bt handlers code)⟩)
      n (.success (.of effect)) finish) : Covers (ConstructiveBodyTryTable.controls c stack env child) (.«TRY_TABLE» bt handlers code) effect ∧ finish=n := by
  obtain ⟨sig,hmem,hraw,hcatches,hbody,_⟩ := ConstructiveBodyControlOriginal.tryTable c stack env bt handlers code effect n finish h
  let ci := signature_inputs c env sig
  let co := signature_outputs c env sig
  let d : context := {c with LABELS:=sig.outputs::c.LABELS}
  let ed : Env d := env.pushLabel sig.outputs co
  let hi : ∀t∈sig.inputs,CandidateValMatch.InTableVal d t := fun t ht =>
    CandidateProvenanceSteps.in_table_val_of_types_eq c d t rfl (ci t ht)
  let ho : ∀t∈sig.outputs,CandidateValMatch.InTableVal d t := fun t ht =>
    CandidateProvenanceSteps.in_table_val_of_types_eq c d t rfl (co t ht)
  obtain ⟨b,hb,he⟩ := hc d ed sig.inputs sig.outputs hi ho code n finish (by simp +arith) hbody
  obtain ⟨cs,hcs,hmcs⟩ := ConstructiveBodyCatchLists.covered_list c env handlers hcatches
  have hsupp := ConstructiveBodyCatchLists.list_support c env cs hmcs
  have realizes : ∃p∈ConstructiveBodyTryTable.controls c stack env child,Produces p (.«TRY_TABLE» bt handlers code) := by
    unfold ConstructiveBodyTryTable.controls
    refine ⟨?p,?mem,?prod⟩
    case mem =>
      apply List.mem_map.mpr
      refine ⟨sig,hmem,?_⟩
      rfl
    case prod =>
      refine ⟨_,⟨cs,hsupp,b,hb,rfl⟩,?_⟩
      simp only [hraw,hcs,he]
  obtain ⟨p,hp,hi⟩ := realizes
  exact ConstructiveBodyFunctionCoverage.from_production c stack (ConstructiveBodyTryTable.controls c stack env child) p _ effect n finish hp hi h

#print axioms block
#print axioms ifElse
#print axioms tryTable
end properties.wasm_module_ok.ConstructiveBodyChildCoverage
