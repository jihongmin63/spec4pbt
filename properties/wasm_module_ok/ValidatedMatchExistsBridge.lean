import properties.wasm_module_ok.ValidatedUnrolledPredecessors
import properties.wasm_module_ok.MatchHeaptypeBasic

set_option autoImplicit false

namespace properties.wasm_module_ok.ValidatedMatchExistsBridge

open properties.wasm_module_ok.ValidatedTypeChain

theorem validated_type_match_exists_of_predecessors
    (c : SpecTec.context) (p : Nat) (dtQ : SpecTec.deftype)
    (start : Nat)
    (hc : ValidatedTypes c) (hp : p < c.TYPES.length)
    (hmatch : ∀ k dtK, k < p → c.TYPES[k]? = some dtK →
      ∃ r : Bool,
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨Bool,
            SpecTec.Call.«$match_deftype» c.TYPES dtK dtQ⟩)
          start (.success (.of r)) start) :
    ∃ dtP : SpecTec.deftype,
    ∃ fin : SpecTec.final,
    ∃ htsU : List SpecTec.heaptype,
    ∃ strtU : SpecTec.strtype,
    ∃ r : Bool,
      c.TYPES[p]? = some dtP ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.subtype, SpecTec.Call.«$unrolldt» dtP⟩)
        start (.success (.of (SpecTec.subtype.SubT fin htsU strtU))) start ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool,
          SpecTec.Call.«$match_heaptype_exists» c.TYPES htsU dtQ⟩)
        start (.success (.of r)) start := by
  obtain ⟨dtP, fin, htsU, strtU, hlookup, hunroll, hedges⟩ :=
    ValidatedUnrolledPredecessors.validated_type_unrolldt_predecessors
      c p start hc hp
  have hheads : ∀ ht ∈ htsU, ∃ r : Bool,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool,
          SpecTec.Call.«$match_heaptype» c.TYPES ht (.DefHT dtQ)⟩)
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
  exact ⟨dtP, fin, htsU, strtU, r, hlookup, hunroll, hexists⟩

end properties.wasm_module_ok.ValidatedMatchExistsBridge
