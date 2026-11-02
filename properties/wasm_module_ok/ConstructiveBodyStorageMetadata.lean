import properties.wasm_module_ok.ConstructiveBodyAggregateMetadata
import properties.wasm_module_ok.ConstructiveBodyEvalReduction
import properties.wasm_module_ok.MatchStorageConditional
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyStorageMetadata
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveBodyAggregateMetadata ConstructiveConstAggregateBuilders

def packed : storagetype → Bool
  | .ValStorageT _ => false
  | .PackStorageT _ => true

theorem packed_call (st : storagetype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body (.call ⟨Bool,Call.«$is_packed_storage_type» st⟩)
      n (.success (.of (packed st))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body (SpecTecExecution.tryClauses (SpecTec.«$is_packed_storage_type_clauses» st)) n _ n
  cases st with
  | ValStorageT t =>
    apply SpecTecExecution.tryClauses_cons_success
    unfold SpecTec.«$is_packed_storage_type:clause:0»
    exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl) (SpecTecExecution.Eval.pure _)
  | PackStorageT pt =>
    apply SpecTecExecution.tryClauses_cons_unmatch
    · unfold SpecTec.«$is_packed_storage_type:clause:0»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by change ¬false=true; decide))
    apply SpecTecExecution.tryClauses_cons_success
    unfold SpecTec.«$is_packed_storage_type:clause:1»
    exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl) (SpecTecExecution.Eval.pure _)

theorem fieldBacked {c : context} (s : StructIndex c) (env : Env c) (f : ConstructiveBodyLookup.Entry s.fields) :
    CandidateValMatch.InTableVal c (UnpackedFieldDecision.unpackedFieldResult f.value) :=
  structInputs s env _ (List.mem_map.mpr ⟨f.value,f.mem,rfl⟩)

def storageMatch (c : context) : storagetype → storagetype → Bool
  | .ValStorageT a,.ValStorageT b => CandidateValMatch.candidateValMatch c a b
  | .PackStorageT a,.PackStorageT b => decide (a=b)
  | _,_ => false

theorem storage_call (c : context) (a b : storagetype) (n : Nat) (env : Env c)
    (ha : CandidateValMatch.InTableVal c (UnpackedFieldDecision.unpackedStorageResult a))
    (hb : CandidateValMatch.InTableVal c (UnpackedFieldDecision.unpackedStorageResult b)) :
    SpecTecExecution.Eval SpecTec.Body (.call ⟨Bool,Call.«$match_storagetype» c.TYPES a b⟩)
      n (.success (.of (storageMatch c a b))) n := by
  cases a with
  | ValStorageT a =>
    cases b with
    | ValStorageT b =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$match_storagetype_clauses» c.TYPES (.ValStorageT a) (.ValStorageT b))) n _ n
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$match_storagetype:clause:0»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      apply SpecTecExecution.Eval.bind_success (CandidateValMatch.candidate_val_match_total c a b n env.ready ha hb)
      exact SpecTecExecution.Eval.pure _
    | PackStorageT b => exact MatchStorageConditional.match_storage_val_pack_total c.TYPES (fun _ _ => false) a b n
  | PackStorageT a =>
    cases b with
    | ValStorageT b => exact MatchStorageConditional.match_storage_pack_val_total c.TYPES (fun _ _ => false) a b n
    | PackStorageT b => exact MatchStorageConditional.match_storage_pack_pair_total c.TYPES (fun _ _ => false) a b n

#print axioms storage_call
end properties.wasm_module_ok.ConstructiveBodyStorageMetadata
