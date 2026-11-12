import properties.wasm_module_not_ok.SubtypeSubTrace
import properties.wasm_module_ok.UnrollInterface

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

theorem subtype_sub_leaf_statx_success (c : SpecTec.context)
    (x x' : Nat) (strt : SpecTec.strtype) (dt : SpecTec.deftype)
    (fin : SpecTec.final) (hts : List SpecTec.heaptype)
    (strt' : SpecTec.strtype) (start middle : Nat)
    (hbound : x' < (SpecTec.context.TYPES c).length)
    (hdt : (SpecTec.context.TYPES c)[x']? = some dt)
    (hunroll : unrollDeftypeResult dt = some (.SubT fin hts strt'))
    (hmatch : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_strtype»
          (SpecTec.context.TYPES c) strt strt'⟩)
      start (.success (.of true)) middle)
    (hbefore : x' < x) (hfin : fin = .NoFinal) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.Subtype_sub_ok' c x strt
          (.VarHT (.StatX x'))⟩)
      start (.success (.of ())) middle := by
  have hu : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.subtype, SpecTec.SpecTecCall.«$unrolldt» dt⟩)
      start (.success (.of (SpecTec.subtype.SubT fin hts strt'))) start := by
    simpa [unrollDeftypeOutcome, hunroll] using unrolldt_total dt start
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.Subtype_sub_ok'_clauses c x strt (.VarHT (.StatX x'))) ())
    start (.success (.of ())) middle
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«Subtype_sub_ok':clause:0» c x strt (.VarHT (.StatX x')))
    start (.success (.of ())) middle
  unfold SpecTec.«Subtype_sub_ok':clause:0»
  simp only [SpecTec.«sub:heaptype:heaptypeVar»,
    SpecTec.«Subtype_sub_ok':rule:downcast:0»,
    SpecTec.«exec:match:typevar:StatX», hdt]
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true (by decide)
  · apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true (by decide)
    · apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true hbound
      · apply SpecTecExecution.Eval.bind_success hu
        apply SpecTecExecution.Eval.bind_success hmatch
        apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true ⟨⟨hbefore, hfin⟩, rfl⟩
        · exact SpecTecExecution.Eval.pure ()

theorem subtype_sub_leaf_statx_success_inv (c : SpecTec.context)
    (x x' : Nat) (strt : SpecTec.strtype) (start finalSupply : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.Subtype_sub_ok' c x strt
          (.VarHT (.StatX x'))⟩)
      start (.success (.of ())) finalSupply) :
    ∃ (dt : SpecTec.deftype) (fin : SpecTec.final)
      (hts : List SpecTec.heaptype) (strt' : SpecTec.strtype),
      x' < (SpecTec.context.TYPES c).length ∧
      (SpecTec.context.TYPES c)[x']? = some dt ∧
      unrollDeftypeResult dt = some (.SubT fin hts strt') ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool,
          SpecTec.SpecTecCall.«$match_strtype»
            (SpecTec.context.TYPES c) strt strt'⟩)
        start (.success (.of true)) finalSupply ∧
      x' < x ∧ fin = .NoFinal := by
  cases h with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (.orElse
        (SpecTec.«Subtype_sub_ok':clause:0» c x strt (.VarHT (.StatX x')))
        (fun _ => .unmatch))
      start (.success (.of ())) finalSupply at hbody
    cases hbody with
    | orElse_success hfirst =>
      unfold SpecTec.«Subtype_sub_ok':clause:0» at hfirst
      simp only [SpecTec.«sub:heaptype:heaptypeVar»,
        SpecTec.«Subtype_sub_ok':rule:downcast:0»,
        SpecTec.«exec:match:typevar:StatX»] at hfirst
      cases hfirst with
      | bind_success hguard1 hrest =>
        cases hguard1 with
        | guard_true _ =>
          cases hrest with
          | bind_success hguard2 hrest =>
            cases hguard2 with
            | guard_true _ =>
              cases hrest with
              | bind_success hguard3 hrest =>
                cases hguard3 with
                | guard_true hbound =>
                  cases hlookup : (SpecTec.context.TYPES c)[x']? with
                  | none =>
                      simp only [hlookup] at hrest
                      cases hrest
                  | some dt =>
                      simp only [hlookup] at hrest
                      cases hrest with
                      | bind_success hunroll hrest =>
                        rename_i unrolled
                        cases unrolled with
                        | SubT fin hts strt' =>
                          cases hrest with
                          | bind_success hmatch hrest =>
                            cases hrest with
                            | bind_success hguard hpure =>
                              cases hpure with
                              | pure =>
                                cases hguard with
                                | guard_true hconditions =>
                                  obtain ⟨hbeforefin, htrue⟩ := hconditions
                                  obtain ⟨hbefore, hfin⟩ := hbeforefin
                                  cases htrue
                                  obtain ⟨hresult, hsupply⟩ :=
                                    (properties.wasm_module_ok.UnrollInterface.unrolldt_success_iff
                                      dt (.SubT fin hts strt') start _).1 hunroll
                                  subst hsupply
                                  exact ⟨dt, fin, hts, strt', hbound, rfl,
                                    hresult, hmatch, hbefore, hfin⟩
    | orElse_unmatch _ htail => cases htail

theorem subtype_sub_leaf_statx_success_iff (c : SpecTec.context)
    (x x' : Nat) (strt : SpecTec.strtype) (start finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.Subtype_sub_ok' c x strt
          (.VarHT (.StatX x'))⟩)
      start (.success (.of ())) finalSupply ↔
    ∃ (dt : SpecTec.deftype) (fin : SpecTec.final)
      (hts : List SpecTec.heaptype) (strt' : SpecTec.strtype),
      x' < (SpecTec.context.TYPES c).length ∧
      (SpecTec.context.TYPES c)[x']? = some dt ∧
      unrollDeftypeResult dt = some (.SubT fin hts strt') ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool,
          SpecTec.SpecTecCall.«$match_strtype»
            (SpecTec.context.TYPES c) strt strt'⟩)
        start (.success (.of true)) finalSupply ∧
      x' < x ∧ fin = .NoFinal := by
  constructor
  · exact subtype_sub_leaf_statx_success_inv c x x' strt start finalSupply
  · rintro ⟨dt, fin, hts, strt', hbound, hdt, hunroll,
      hmatch, hbefore, hfin⟩
    exact subtype_sub_leaf_statx_success c x x' strt dt fin hts strt'
      start finalSupply hbound hdt hunroll hmatch hbefore hfin

theorem subtype_sub_leaf_success_shape (c : SpecTec.context)
    (x : Nat) (strt : SpecTec.strtype) (ht : SpecTec.heaptype)
    (start finalSupply : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Subtype_sub_ok' c x strt ht⟩)
      start (.success (.of ())) finalSupply) :
    ∃ x' : Nat, ht = .VarHT (.StatX x') := by
  cases h with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (.orElse (SpecTec.«Subtype_sub_ok':clause:0» c x strt ht)
        (fun _ => .unmatch))
      start (.success (.of ())) finalSupply at hbody
    cases hbody with
    | orElse_success hfirst =>
      unfold SpecTec.«Subtype_sub_ok':clause:0» at hfirst
      cases hfirst with
      | bind_success hguard hrest =>
        cases hguard with
        | guard_true hvar =>
          cases ht with
          | VarHT tv =>
              cases tv with
              | StatX n => exact ⟨n, rfl⟩
              | RecX n =>
                  simp only [SpecTec.«Subtype_sub_ok':rule:downcast:0»,
                    SpecTec.«exec:match:typevar:StatX»] at hrest
                  cases hrest with
                  | bind_success hguard2 _ =>
                      cases hguard2 with
                      | guard_true hbad => cases hbad
          | _ =>
              simp [SpecTec.«sub:heaptype:heaptypeVar»] at hvar
    | orElse_unmatch _ htail => cases htail

theorem subtype_sub_leaf_success_iff (c : SpecTec.context)
    (x : Nat) (strt : SpecTec.strtype) (ht : SpecTec.heaptype)
    (start finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Subtype_sub_ok' c x strt ht⟩)
      start (.success (.of ())) finalSupply ↔
    ∃ (x' : Nat) (dt : SpecTec.deftype) (fin : SpecTec.final)
      (hts : List SpecTec.heaptype) (strt' : SpecTec.strtype),
      ht = .VarHT (.StatX x') ∧
      x' < (SpecTec.context.TYPES c).length ∧
      (SpecTec.context.TYPES c)[x']? = some dt ∧
      unrollDeftypeResult dt = some (.SubT fin hts strt') ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool,
          SpecTec.SpecTecCall.«$match_strtype»
            (SpecTec.context.TYPES c) strt strt'⟩)
        start (.success (.of true)) finalSupply ∧
      x' < x ∧ fin = .NoFinal := by
  constructor
  · intro h
    obtain ⟨x', rfl⟩ := subtype_sub_leaf_success_shape c x strt ht
      start finalSupply h
    obtain ⟨dt, fin, hts, strt', hbound, hdt, hunroll,
      hmatch, hbefore, hfin⟩ :=
      (subtype_sub_leaf_statx_success_iff c x x' strt
        start finalSupply).1 h
    exact ⟨x', dt, fin, hts, strt', rfl, hbound, hdt,
      hunroll, hmatch, hbefore, hfin⟩
  · rintro ⟨x', dt, fin, hts, strt', rfl, hbound, hdt,
      hunroll, hmatch, hbefore, hfin⟩
    exact (subtype_sub_leaf_statx_success_iff c x x' strt
      start finalSupply).2
      ⟨dt, fin, hts, strt', hbound, hdt,
        hunroll, hmatch, hbefore, hfin⟩

end properties.wasm_module_not_ok.Rejection
