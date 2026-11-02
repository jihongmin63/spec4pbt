import properties.wasm_module_ok.TypesPrefixValidation
import properties.wasm_module_ok.RectypeLengthValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.ValidatedTypeChain

inductive ValidatedTypes : SpecTec.context → Prop where
  | seed (c : SpecTec.context) (h : c.TYPES = []) : ValidatedTypes c
  | append (c result : SpecTec.context)
      (sts : List SpecTec.subtype) (start finish : Nat)
      (hc : ValidatedTypes c)
      (h : SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.context,
          SpecTec.SpecTecCall.Rectype_ok c (.RecT sts)⟩)
        start (.success (.of result)) finish) :
      ValidatedTypes result

theorem types_ok_nil_eq
    (c result : SpecTec.context) (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Types_ok c []⟩)
      start (.success (.of result)) finish) :
    result = c := by
  cases h with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (.orElse (SpecTec.«Types_ok:clause:0» c [])
        (fun _ => SpecTecExecution.firstSuccess
          [fun _ => SpecTec.«Types_ok:clause:1» c []] ()))
      start (.success (.of result)) finish at hbody
    cases hbody with
    | orElse_success hfirst =>
      unfold SpecTec.«Types_ok:clause:0» at hfirst
      cases hfirst with
      | bind_success hguard _ =>
        cases hguard with
        | guard_true hcond => simp at hcond
    | orElse_unmatch _ htail =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse (SpecTec.«Types_ok:clause:1» c [])
          (fun _ => .unmatch))
        start (.success (.of result)) finish at htail
      cases htail with
      | orElse_success hsecond =>
        unfold SpecTec.«Types_ok:clause:1» at hsecond
        cases hsecond with
        | bind_success _ hpure =>
          cases hpure
          rfl
      | orElse_unmatch _ hnone => cases hnone

theorem types_ok_preserves
    (c result : SpecTec.context) (ts : List SpecTec.type)
    (start finish : Nat)
    (hc : ValidatedTypes c)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Types_ok c ts⟩)
      start (.success (.of result)) finish) :
    ValidatedTypes result := by
  induction ts generalizing c result start finish with
  | nil =>
      have heq := types_ok_nil_eq c result start finish h
      subst result
      exact hc
  | cons t ts ih =>
      cases t with
      | RecT sts =>
        obtain ⟨middle, next, hhead, htail⟩ :=
          TypesPrefixValidation.types_ok_cons_trace
            c result (.RecT sts) ts start finish h
        have hrect :=
          TypesPrefixValidation.type_ok_rectype_trace
            c next sts start middle hhead
        exact ih next result middle finish
          (ValidatedTypes.append c next sts start middle hc hrect) htail

theorem validated_types_position_provenance
    (c : SpecTec.context) (p : Nat)
    (hc : ValidatedTypes c) (hp : p < c.TYPES.length) :
    ∃ before after : SpecTec.context,
    ∃ sts : List SpecTec.subtype,
    ∃ start finish i : Nat,
    ∃ tail : List SpecTec.deftype,
      ValidatedTypes before ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.context,
          SpecTec.SpecTecCall.Rectype_ok before (.RecT sts)⟩)
        start (.success (.of after)) finish ∧
      p = before.TYPES.length + i ∧ i < sts.length ∧
      c.TYPES = after.TYPES ++ tail := by
  induction hc generalizing p with
  | seed c hnil =>
      simp [hnil] at hp
  | append before after sts start finish hbefore hrect ih =>
      obtain ⟨dts, hafterContext, hlen⟩ :=
        RectypeLengthValidation.rectype_ok_appended_types_length
          before after sts start finish hrect
      have hafter : after.TYPES = before.TYPES ++ dts :=
        congrArg SpecTec.context.TYPES hafterContext
      by_cases hold : p < before.TYPES.length
      · obtain ⟨base, groupOut, group, s, f, i, tail,
            hbase, hgroup, hpos, hi, hprefix⟩ := ih p hold
        refine ⟨base, groupOut, group, s, f, i, tail ++ dts,
          hbase, hgroup, hpos, hi, ?_⟩
        rw [hafter, hprefix, List.append_assoc]
      · have hplen : p < before.TYPES.length + dts.length := by
          simpa [hafter, List.length_append] using hp
        have hi : p - before.TYPES.length < sts.length := by
          omega
        have hpos : p = before.TYPES.length + (p - before.TYPES.length) := by
          omega
        refine ⟨before, after, sts, start, finish,
          p - before.TYPES.length, [], hbefore, hrect, hpos, hi, ?_⟩
        simp

theorem validated_types_position_source
    (c : SpecTec.context) (p : Nat)
    (hc : ValidatedTypes c) (hp : p < c.TYPES.length) :
    ∃ before after : SpecTec.context,
    ∃ sts : List SpecTec.subtype,
    ∃ start finish i : Nat,
    ∃ tail : List SpecTec.deftype,
    ∃ fin : SpecTec.final,
    ∃ hts : List SpecTec.heaptype,
    ∃ strt : SpecTec.strtype,
      ValidatedTypes before ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.context,
          SpecTec.SpecTecCall.Rectype_ok before (.RecT sts)⟩)
        start (.success (.of after)) finish ∧
      p = before.TYPES.length + i ∧ i < sts.length ∧
      sts[i]? = some (.SubT fin hts strt) ∧
      c.TYPES = after.TYPES ++ tail := by
  obtain ⟨before, after, sts, start, finish, i, tail,
    hbefore, hrect, hpos, hi, hprefix⟩ :=
    validated_types_position_provenance c p hc hp
  have hsome : sts[i]? = some sts[i] := List.getElem?_eq_getElem hi
  cases hsub : sts[i] with
  | SubT fin hts strt =>
      refine ⟨before, after, sts, start, finish, i, tail,
        fin, hts, strt, hbefore, hrect, hpos, hi, ?_, hprefix⟩
      rw [hsome, hsub]

end properties.wasm_module_ok.ValidatedTypeChain
