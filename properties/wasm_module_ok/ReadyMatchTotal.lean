import properties.wasm_module_ok.ReadyTypeInterfaces
import properties.wasm_module_ok.MatchHeaptypeBasic

set_option autoImplicit false

namespace properties.wasm_module_ok.ReadyMatchTotal

open properties.wasm_module_not_ok.Rejection

private theorem ready_match_exists_of_predecessors
    (c : SpecTec.context) (p : Nat) (dtQ : SpecTec.deftype)
    (start : Nat) (hready : CandidateTypeReady.Ready c)
    (hp : p < c.TYPES.length)
    (hmatch : ∀ k dtK, k < p → c.TYPES[k]? = some dtK →
      ∃ r : Bool,
        SpecTecExecution.Eval SpecTec.specTecProgram
          (.call ⟨Bool,
            SpecTec.SpecTecCall.«$match_deftype» c.TYPES dtK dtQ⟩)
          start (.success (.of r)) start) :
    ∃ dtP : SpecTec.deftype,
    ∃ fin : SpecTec.final,
    ∃ htsU : List SpecTec.heaptype,
    ∃ strtU : SpecTec.strtype,
    ∃ r : Bool,
      c.TYPES[p]? = some dtP ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.subtype, SpecTec.SpecTecCall.«$unrolldt» dtP⟩)
        start (.success (.of (SpecTec.subtype.SubT fin htsU strtU))) start ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool,
          SpecTec.SpecTecCall.«$match_heaptype_exists» c.TYPES htsU dtQ⟩)
        start (.success (.of r)) start := by
  obtain ⟨dtP, fin, htsU, strtU, hlookup, hunroll, hedges⟩ :=
    hready.unrolledPredecessors p hp
  have hunrollEval :=
    (UnrollInterface.unrolldt_success_iff
      dtP (.SubT fin htsU strtU) start start).2 ⟨hunroll, rfl⟩
  have hheads : ∀ ht ∈ htsU, ∃ r : Bool,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool,
          SpecTec.SpecTecCall.«$match_heaptype» c.TYPES ht (.DefHT dtQ)⟩)
        start (.success (.of r)) start := by
    intro ht hmem
    obtain ⟨j, hget⟩ := List.mem_iff_getElem?.mp hmem
    have hj : j < htsU.length :=
      (List.getElem?_eq_some_iff.mp hget).choose
    obtain ⟨k, dtK, hkp, hcPred, hgetK⟩ := hedges j hj
    have hht : ht = .DefHT dtK :=
      Option.some.inj (hget.symm.trans hgetK)
    subst ht
    obtain ⟨r, hr⟩ := hmatch k dtK hkp hcPred
    exact ⟨r,
      MatchHeaptypeBasic.match_heaptype_def_def_total_of_match_deftype
        c.TYPES dtK dtQ r start hr⟩
  obtain ⟨r, hexists⟩ :=
    MatchHeaptypeBasic.match_heaptype_exists_total_of_heads
      c.TYPES dtQ htsU start hheads
  exact ⟨dtP, fin, htsU, strtU, r, hlookup, hunrollEval, hexists⟩

private theorem ready_match_deftype_of_predecessors
    (c : SpecTec.context) (p : Nat)
    (dtP dtQ : SpecTec.deftype) (start : Nat)
    (hready : CandidateTypeReady.Ready c)
    (hp : p < c.TYPES.length)
    (hlookup : c.TYPES[p]? = some dtP)
    (hQ : ∃ q, q < c.TYPES.length ∧ c.TYPES[q]? = some dtQ)
    (hmatch : ∀ k dtK, k < p → c.TYPES[k]? = some dtK →
      ∃ r : Bool,
        SpecTecExecution.Eval SpecTec.specTecProgram
          (.call ⟨Bool,
            SpecTec.SpecTecCall.«$match_deftype» c.TYPES dtK dtQ⟩)
          start (.success (.of r)) start) :
    ∃ r : Bool,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool,
          SpecTec.SpecTecCall.«$match_deftype» c.TYPES dtP dtQ⟩)
        start (.success (.of r)) start := by
  by_cases heq : dtP = dtQ
  · subst dtQ
    exact ⟨true,
      MatchHeaptypeBasic.match_deftype_refl_total c.TYPES dtP start⟩
  have hsP :=
    ReadyTypeInterfaces.ready_substitution_fixed c hready p start dtP hp hlookup
  obtain ⟨q, hq, hlookupQ⟩ := hQ
  have hsQ :=
    ReadyTypeInterfaces.ready_substitution_fixed c hready q start dtQ hq hlookupQ
  obtain ⟨dtP', fin, htsU, strtU, r, hlookup', hunroll, hexists⟩ :=
    ready_match_exists_of_predecessors c p dtQ start hready hp hmatch
  have hdtEq : dtP' = dtP :=
    Option.some.inj (hlookup'.symm.trans hlookup)
  subst dtP'
  exact ⟨r,
    MatchHeaptypeBasic.match_deftype_neq_subst_neq_total_of_exists
      c.TYPES dtP dtQ dtP dtQ fin htsU strtU r start
      heq hsP hsQ heq hunroll hexists⟩

theorem ready_match_deftype_total
    (c : SpecTec.context) (p q start : Nat)
    (dtP dtQ : SpecTec.deftype)
    (hready : CandidateTypeReady.Ready c)
    (hp : p < c.TYPES.length) (hq : q < c.TYPES.length)
    (hP : c.TYPES[p]? = some dtP)
    (hQ : c.TYPES[q]? = some dtQ) :
    ∃ r : Bool,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool,
          SpecTec.SpecTecCall.«$match_deftype» c.TYPES dtP dtQ⟩)
        start (.success (.of r)) start := by
  have hfixed : ∀ k dt, k < c.TYPES.length →
      c.TYPES[k]? = some dt →
      ∃ r : Bool,
        SpecTecExecution.Eval SpecTec.specTecProgram
          (.call ⟨Bool,
            SpecTec.SpecTecCall.«$match_deftype» c.TYPES dt dtQ⟩)
          start (.success (.of r)) start := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
        intro dt hk hlookup
        apply ready_match_deftype_of_predecessors
          c k dt dtQ start hready hk hlookup ⟨q, hq, hQ⟩
        intro i dtI hik hiLookup
        exact ih i hik dtI (by omega) hiLookup
  exact hfixed p dtP hp hP

end properties.wasm_module_ok.ReadyMatchTotal
