import properties.wasm_module_ok.RectypeRangeValidation
import properties.wasm_module_not_ok.RolldtValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.RectypeLengthValidation

open properties.wasm_module_not_ok.Rejection

theorem rolledDefs_length (rect : SpecTec.rectype) (i count : Nat) :
    (rolledDefs rect i count).length = count := by
  induction count generalizing i with
  | zero => rfl
  | succ count ih => simp [rolledDefs, ih]

theorem rollDeftypes_length (x : Nat) (sts : List SpecTec.subtype) :
    (rollDeftypes x (.RecT sts)).length = sts.length := by
  simp [rollDeftypes, rollRectypeAt, rollRectype,
    rolledDefs_length, rollSubtypes]

theorem rolldt_success_length (x : Nat) (sts : List SpecTec.subtype)
    (dts : List SpecTec.deftype) (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨List SpecTec.deftype,
        SpecTec.SpecTecCall.«$rolldt» x (.RecT sts)⟩)
      start (.success (.of dts)) finish) :
    dts.length = sts.length := by
  obtain ⟨hout, _⟩ := rolldt_deterministic x (.RecT sts)
    start finish (.success (.of dts)) h
  cases hout
  exact rollDeftypes_length x sts

theorem rectype_subst_iter_length
    (c : SpecTec.context) (rolled substituted : List SpecTec.deftype)
    (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨List SpecTec.deftype,
        SpecTec.SpecTecCall.«Rectype_ok:rule:iter:2» c rolled⟩)
      start (.success (.of substituted)) finish) :
    substituted.length = rolled.length := by
  induction rolled generalizing substituted start finish with
  | nil =>
      cases h with
      | call hbody =>
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTecExecution.firstSuccess
            (SpecTec.«Rectype_ok:rule:iter:2_clauses» c []) ())
          start (.success (.of substituted)) finish at hbody
        obtain ⟨idx, hselected⟩ :=
          (SpecTecExecution.firstSuccess_success_iff
            (SpecTec.«Rectype_ok:rule:iter:2_clauses» c []) ()
            start (.of substituted) finish).1 hbody
        unfold SpecTec.«Rectype_ok:rule:iter:2_clauses» at hselected
        cases hselected with
        | here h0 =>
          unfold SpecTec.«Rectype_ok:rule:iter:2:clause:0» at h0
          cases h0
          rfl
        | next _ hrest =>
          cases hrest with
          | here h1 =>
            unfold SpecTec.«Rectype_ok:rule:iter:2:clause:1» at h1
            cases h1
          | next _ hrest => cases hrest
  | cons hd tl ih =>
      cases h with
      | call hbody =>
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTecExecution.firstSuccess
            (SpecTec.«Rectype_ok:rule:iter:2_clauses» c (hd :: tl)) ())
          start (.success (.of substituted)) finish at hbody
        obtain ⟨idx, hselected⟩ :=
          (SpecTecExecution.firstSuccess_success_iff
            (SpecTec.«Rectype_ok:rule:iter:2_clauses» c (hd :: tl)) ()
            start (.of substituted) finish).1 hbody
        unfold SpecTec.«Rectype_ok:rule:iter:2_clauses» at hselected
        cases hselected with
        | here h0 =>
          unfold SpecTec.«Rectype_ok:rule:iter:2:clause:0» at h0
          cases h0
        | next _ hrest =>
          cases hrest with
          | here h1 =>
            unfold SpecTec.«Rectype_ok:rule:iter:2:clause:1» at h1
            cases h1 with
            | bind_success _ htail =>
              cases htail with
              | bind_success hrec hpure =>
                cases hpure
                simp [ih _ _ _ hrec]
          | next _ hrest => cases hrest

theorem rectype_ok_appended_types_length
    (c c' : SpecTec.context) (sts : List SpecTec.subtype)
    (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.Rectype_ok c (.RecT sts)⟩)
      start (.success (.of c')) finish) :
    ∃ dts : List SpecTec.deftype,
      c' = {c with TYPES := c.TYPES ++ dts} ∧
      dts.length = sts.length := by
  cases h with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.Rectype_ok_clauses c (.RecT sts)) ())
      start (.success (.of c')) finish at hbody
    obtain ⟨idx, hselected⟩ :=
      (SpecTecExecution.firstSuccess_success_iff
        (SpecTec.Rectype_ok_clauses c (.RecT sts)) ()
        start (.of c') finish).1 hbody
    unfold SpecTec.Rectype_ok_clauses at hselected
    cases hselected with
    | here h0 =>
      unfold SpecTec.«Rectype_ok:clause:0» at h0
      dsimp only at h0
      cases h0 with
      | bind_success hrange h1 =>
        dsimp only at h1
        cases h1 with
        | bind_success hroll h2 =>
          rename_i rolled
          have hrolled := rolldt_success_length c.TYPES.length sts rolled _ _ hroll
          dsimp only at h2
          cases h2 with
          | bind_success hsubst h3 =>
            rename_i dts
            have hdts := rectype_subst_iter_length c rolled dts _ _ hsubst
            dsimp only at h3
            cases h3 with
            | bind_success hiter5 h4 =>
              dsimp only at h4
              cases h4 with
              | bind_success hguard h5 =>
                dsimp only at h5
                cases h5 with
                | bind_success hiter6 h6 =>
                  rename_i v
                  cases h6
                  cases v
                  exact ⟨dts, rfl, hdts.trans hrolled⟩
    | next _ hrest => cases hrest

end properties.wasm_module_ok.RectypeLengthValidation
