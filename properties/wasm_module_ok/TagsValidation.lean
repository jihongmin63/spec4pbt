import properties.wasm_module_ok.TagtypeValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.TagsValidation

def tagDeclResult (c : SpecTec.context) (t : SpecTec.tag) :
    Option SpecTec.context :=
  match c.TYPES[t.TGTYPE]? with
  | none => none
  | some dt =>
      if TagtypeValidation.tagtypeValid (.TagT dt) then
        some { c with TAGS := c.TAGS ++ [.TagT dt] }
      else none

def tagDeclOutcome (c : SpecTec.context) (t : SpecTec.tag) :
    SpecTecExecution.Outcome SpecTecExecution.Value :=
  match tagDeclResult c t with
  | none => .unmatch
  | some result => .success (.of result)

theorem tag_ok_total (c : SpecTec.context)
    (t : SpecTec.tag) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Tag_ok c t⟩)
      n (tagDeclOutcome c t) n := by
  cases hget : c.TYPES[t.TGTYPE]? with
  | none =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.Tag_ok_clauses c t))
      n (tagDeclOutcome c t) n
    simp only [tagDeclOutcome, tagDeclResult, hget]
    apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«Tag_ok:clause:0» c t) n .unmatch n
      unfold SpecTec.«Tag_ok:clause:0»
      apply SpecTecExecution.Eval.bind_unmatch
      apply SpecTecExecution.Eval.guard_false
      have hnot : ¬ t.TGTYPE < c.TYPES.length := by
        simpa using (List.getElem?_eq_none_iff.mp hget)
      exact hnot
    · exact SpecTecExecution.tryClauses_nil n
  | some dt =>
    have hbound : t.TGTYPE < c.TYPES.length :=
      (List.getElem?_eq_some_iff.mp hget).1
    cases hv : TagtypeValidation.tagtypeValid (.TagT dt) with
    | true =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.Tag_ok_clauses c t))
        n (tagDeclOutcome c t) n
      simp only [tagDeclOutcome, tagDeclResult, hget, hv, ite_true]
      apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«Tag_ok:clause:0» c t)
        n (.success (.of { c with TAGS := c.TAGS ++ [SpecTec.tagtype.TagT dt] })) n
      unfold SpecTec.«Tag_ok:clause:0»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true hbound
      · rw [hget]
        apply SpecTecExecution.Eval.bind_success
        · exact (TagtypeValidation.tagtype_success_iff_valid
            c (.TagT dt) n n).2 ⟨hv, rfl⟩
        · exact SpecTecExecution.Eval.pure
            { c with TAGS := c.TAGS ++ [SpecTec.tagtype.TagT dt] }
    | false =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.Tag_ok_clauses c t))
        n (tagDeclOutcome c t) n
      simp only [tagDeclOutcome, tagDeclResult, hget, hv]
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«Tag_ok:clause:0» c t) n .unmatch n
        unfold SpecTec.«Tag_ok:clause:0»
        apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true hbound
        · rw [hget]
          apply SpecTecExecution.Eval.bind_unmatch
          simpa [TagtypeValidation.tagtypeOutcome, hv] using
            TagtypeValidation.tagtype_total c (.TagT dt) n
      · exact SpecTecExecution.tryClauses_nil n

theorem tag_ok_success_iff_result (c : SpecTec.context)
    (t : SpecTec.tag) (result : SpecTec.context)
    (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Tag_ok c t⟩)
      n (.success (.of result)) finalSupply ↔
    tagDeclResult c t = some result ∧ finalSupply = n := by
  constructor
  · intro h
    obtain ⟨hout, hsupply⟩ :=
      properties.wasm_module_ok.Execution.eval_deterministic h (tag_ok_total c t n)
    cases hr : tagDeclResult c t with
    | none => simp [tagDeclOutcome, hr] at hout
    | some result' =>
      simp [tagDeclOutcome, hr] at hout
      cases hout
      exact ⟨rfl, hsupply⟩
  · rintro ⟨hr, rfl⟩
    simpa [tagDeclOutcome, hr] using tag_ok_total c t finalSupply

theorem tag_ok_none (c : SpecTec.context)
    (t : SpecTec.tag) (n : Nat)
    (hr : tagDeclResult c t = none) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Tag_ok c t⟩)
      n .unmatch n := by
  simpa [tagDeclOutcome, hr] using tag_ok_total c t n

def tagsResult (c : SpecTec.context) :
    List SpecTec.tag → Option SpecTec.context
  | [] => some c
  | t :: ts =>
      (tagDeclResult c t).bind fun c₁ => tagsResult c₁ ts

def tagsOutcome (c : SpecTec.context) (ts : List SpecTec.tag) :
    SpecTecExecution.Outcome SpecTecExecution.Value :=
  match tagsResult c ts with
  | none => .unmatch
  | some result => .success (.of result)

theorem tags_total (c : SpecTec.context)
    (ts : List SpecTec.tag) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Tags_ok c ts⟩)
      n (tagsOutcome c ts) n := by
  induction ts generalizing c with
  | nil =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.Tags_ok_clauses c []))
      n (tagsOutcome c []) n
    apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«Tags_ok:clause:0» c []) n .unmatch n
      unfold SpecTec.«Tags_ok:clause:0»
      apply SpecTecExecution.Eval.bind_unmatch
      apply SpecTecExecution.Eval.guard_false
      simp
    · apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«Tags_ok:clause:1» c [])
        n (tagsOutcome c []) n
      unfold SpecTec.«Tags_ok:clause:1»
      simp only [tagsOutcome, tagsResult]
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · exact SpecTecExecution.Eval.pure c
  | cons t ts ih =>
    cases hhead : tagDeclResult c t with
    | none =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.Tags_ok_clauses c (t :: ts)))
        n (tagsOutcome c (t :: ts)) n
      simp only [tagsOutcome, tagsResult, hhead, Option.bind_none]
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«Tags_ok:clause:0» c (t :: ts)) n .unmatch n
        unfold SpecTec.«Tags_ok:clause:0»
        apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true rfl
        · apply SpecTecExecution.Eval.bind_unmatch
          exact tag_ok_none c t n hhead
      · apply SpecTecExecution.tryClauses_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.Body
            (SpecTec.«Tags_ok:clause:1» c (t :: ts)) n .unmatch n
          unfold SpecTec.«Tags_ok:clause:1»
          apply SpecTecExecution.Eval.bind_unmatch
          apply SpecTecExecution.Eval.guard_false
          simp
        · exact SpecTecExecution.tryClauses_nil n
    | some c₁ =>
      cases htail : tagsResult c₁ ts with
      | none =>
        apply SpecTecExecution.Eval.call
        change SpecTecExecution.Eval SpecTec.Body
          (SpecTecExecution.tryClauses
            (SpecTec.Tags_ok_clauses c (t :: ts)))
          n (tagsOutcome c (t :: ts)) n
        simp only [tagsOutcome, tagsResult, hhead,
          Option.bind_some, htail]
        apply SpecTecExecution.tryClauses_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.Body
            (SpecTec.«Tags_ok:clause:0» c (t :: ts)) n .unmatch n
          unfold SpecTec.«Tags_ok:clause:0»
          apply SpecTecExecution.Eval.bind_success
          · exact SpecTecExecution.Eval.guard_true rfl
          · apply SpecTecExecution.Eval.bind_success
            · exact (tag_ok_success_iff_result c t c₁ n n).2 ⟨hhead, rfl⟩
            · apply SpecTecExecution.Eval.bind_unmatch
              simpa [tagsOutcome, htail] using ih c₁
        · apply SpecTecExecution.tryClauses_cons_unmatch
          · change SpecTecExecution.Eval SpecTec.Body
              (SpecTec.«Tags_ok:clause:1» c (t :: ts)) n .unmatch n
            unfold SpecTec.«Tags_ok:clause:1»
            apply SpecTecExecution.Eval.bind_unmatch
            apply SpecTecExecution.Eval.guard_false
            simp
          · exact SpecTecExecution.tryClauses_nil n
      | some result =>
        apply SpecTecExecution.Eval.call
        change SpecTecExecution.Eval SpecTec.Body
          (SpecTecExecution.tryClauses
            (SpecTec.Tags_ok_clauses c (t :: ts)))
          n (tagsOutcome c (t :: ts)) n
        simp only [tagsOutcome, tagsResult, hhead,
          Option.bind_some, htail]
        apply SpecTecExecution.tryClauses_cons_success
        change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«Tags_ok:clause:0» c (t :: ts))
          n (.success (.of result)) n
        unfold SpecTec.«Tags_ok:clause:0»
        apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true rfl
        · apply SpecTecExecution.Eval.bind_success
          · exact (tag_ok_success_iff_result c t c₁ n n).2 ⟨hhead, rfl⟩
          · apply SpecTecExecution.Eval.bind_success
            · simpa [tagsOutcome, htail] using ih c₁
            · exact SpecTecExecution.Eval.pure result

theorem tags_success_iff_result (c : SpecTec.context)
    (ts : List SpecTec.tag) (result : SpecTec.context)
    (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Tags_ok c ts⟩)
      n (.success (.of result)) finalSupply ↔
    tagsResult c ts = some result ∧ finalSupply = n := by
  constructor
  · intro h
    obtain ⟨hout, hsupply⟩ :=
      properties.wasm_module_ok.Execution.eval_deterministic h (tags_total c ts n)
    cases hr : tagsResult c ts with
    | none => simp [tagsOutcome, hr] at hout
    | some result' =>
      simp [tagsOutcome, hr] at hout
      cases hout
      exact ⟨rfl, hsupply⟩
  · rintro ⟨hr, rfl⟩
    simpa [tagsOutcome, hr] using tags_total c ts finalSupply

theorem tags_none (c : SpecTec.context)
    (ts : List SpecTec.tag) (n : Nat)
    (hr : tagsResult c ts = none) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Tags_ok c ts⟩)
      n .unmatch n := by
  simpa [tagsOutcome, hr] using tags_total c ts n

end properties.wasm_module_ok.TagsValidation
