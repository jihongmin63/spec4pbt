import properties.wasm_module_ok.FreeRefsValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.FreeUnionValidation

theorem nat_compare_eq (x y : Nat) :
    specTecValueCompare x y = .eq → x = y := by
  intro h
  change
    (match (match compare (Int.ofNat x) (Int.ofNat y) with
      | Ordering.eq => Ordering.eq | order => order) with
      | Ordering.eq => Ordering.eq | order => order) = Ordering.eq at h
  cases hc : compare (Int.ofNat x) (Int.ofNat y) with
  | lt => rw [hc] at h; cases h
  | eq =>
      have heq : (Int.ofNat x) = Int.ofNat y :=
        Int.compare_eq_eq.mp hc
      exact Int.ofNat_inj.mp heq
  | gt => rw [hc] at h; cases h

theorem mem_set_insert_of_mem (value x : Nat) (xs : List Nat)
    (hx : x ∈ xs) : x ∈ specTecSetInsert value xs := by
  induction xs with
  | nil => cases hx
  | cons head tail ih =>
      rcases List.mem_cons.mp hx with h | h
      · subst x
        cases hc : specTecValueCompare value head with
        | eq => simp [specTecSetInsert, hc]
        | lt => simp [specTecSetInsert, hc]
        | gt => simp [specTecSetInsert, hc]
      · cases hc : specTecValueCompare value head with
        | eq => simp [specTecSetInsert, hc, h]
        | lt => simp [specTecSetInsert, hc, h]
        | gt => simpa [specTecSetInsert, hc] using Or.inr (ih h)

theorem mem_set_insert_self (x : Nat) (xs : List Nat) :
    x ∈ specTecSetInsert x xs := by
  induction xs with
  | nil => simp [specTecSetInsert]
  | cons head tail ih =>
      cases hc : specTecValueCompare x head with
      | eq =>
          have heq := nat_compare_eq x head hc
          subst x
          simp [specTecSetInsert, hc]
      | lt => simp [specTecSetInsert, hc]
      | gt => simpa [specTecSetInsert, hc] using Or.inr ih

theorem mem_set_normalize (x : Nat) (xs : List Nat)
    (hx : x ∈ xs) : x ∈ specTecSetNormalize xs := by
  induction xs with
  | nil => cases hx
  | cons head tail ih =>
      rcases List.mem_cons.mp hx with h | h
      · subst x
        change head ∈ specTecSetInsert head (specTecSetNormalize tail)
        exact mem_set_insert_self head _
      · change x ∈ specTecSetInsert head (specTecSetNormalize tail)
        exact mem_set_insert_of_mem head x _ (ih h)

theorem mem_set_union (x : Nat) (left right : List Nat)
    (hx : x ∈ left ∨ x ∈ right) :
    x ∈ specTecSetUnion left right := by
  exact mem_set_normalize x (left ++ right) (List.mem_append.mpr hx)

def unionFree (a b : SpecTec.free) : SpecTec.free :=
  { TYPES := SpecTec.«$union_set» a.TYPES b.TYPES
    GLOBALS := SpecTec.«$union_set» a.GLOBALS b.GLOBALS
    TABLES := SpecTec.«$union_set» a.TABLES b.TABLES
    MEMS := SpecTec.«$union_set» a.MEMS b.MEMS
    TAGS := SpecTec.«$union_set» a.TAGS b.TAGS
    FUNCS := SpecTec.«$union_set» a.FUNCS b.FUNCS
    ELEMS := SpecTec.«$union_set» a.ELEMS b.ELEMS
    DATAS := SpecTec.«$union_set» a.DATAS b.DATAS
    LOCALS := SpecTec.«$union_set» a.LOCALS b.LOCALS
    LABELS := SpecTec.«$union_set» a.LABELS b.LABELS }

def HasFunc (free : SpecTec.free) (x : SpecTec.funcidx) : Prop :=
  match free.FUNCS with
  | .«`{ % `}» xs => x ∈ xs

theorem hasFunc_union (a b : SpecTec.free) (x : SpecTec.funcidx)
    (h : HasFunc a x ∨ HasFunc b x) : HasFunc (unionFree a b) x := by
  cases ha : a.FUNCS with
  | «`{ % `}» as =>
    cases hb : b.FUNCS with
    | «`{ % `}» bs =>
      simp only [HasFunc, unionFree, ha, hb, SpecTec.«$union_set»] at h ⊢
      exact mem_set_union x as bs h

theorem free_union_total (a b : SpecTec.free) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.free, SpecTec.Call.«$free_union» a b⟩)
      n (.success (.of (unionFree a b))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses (SpecTec.«$free_union_clauses» a b))
    n (.success (.of (unionFree a b))) n
  apply SpecTecExecution.tryClauses_cons_success
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«$free_union:clause:0» a b)
    n (.success (.of (unionFree a b))) n
  simpa [SpecTec.«$free_union:clause:0», unionFree] using
    (SpecTecExecution.Eval.pure (unionFree a b) (n := n))

theorem free_union_success_iff (a b result : SpecTec.free)
    (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.free, SpecTec.Call.«$free_union» a b⟩)
      n (.success (.of result)) finalSupply ↔
    result = unionFree a b ∧ finalSupply = n := by
  constructor
  · intro h
    obtain ⟨hout, hsupply⟩ :=
      properties.wasm_module_ok.Execution.eval_deterministic h (free_union_total a b n)
    cases hout
    exact ⟨rfl, hsupply⟩
  · rintro ⟨rfl, rfl⟩
    exact free_union_total a b finalSupply

theorem free_union_preserves_funcs (a b result : SpecTec.free)
    (x : SpecTec.funcidx) (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.free, SpecTec.Call.«$free_union» a b⟩)
      n (.success (.of result)) finalSupply)
    (h : HasFunc a x ∨ HasFunc b x) : HasFunc result x := by
  obtain ⟨rfl, _⟩ := (free_union_success_iff a b result n finalSupply).mp hcall
  exact hasFunc_union a b x h

def unionsFree (fs : List SpecTec.free) : SpecTec.free :=
  fs.foldr unionFree properties.wasm_module_not_ok.Rejection.emptyFree

theorem free_unions_total (fs : List SpecTec.free) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.free, SpecTec.Call.«$free_unions» fs⟩)
      n (.success (.of (unionsFree fs))) n := by
  induction fs with
  | nil =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$free_unions_clauses» []))
        n (.success (.of (unionsFree []))) n
      apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$free_unions:clause:0» [])
        n (.success (.of (unionsFree []))) n
      unfold SpecTec.«$free_unions:clause:0»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true (by simp)
      apply SpecTecExecution.Eval.bind_success
        (properties.wasm_module_not_ok.Rejection.free_empty_total n)
      exact SpecTecExecution.Eval.pure _
  | cons head tail ih =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$free_unions_clauses» (head :: tail)))
        n (.success (.of (unionsFree (head :: tail)))) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$free_unions:clause:0» (head :: tail)) n .unmatch n
        unfold SpecTec.«$free_unions:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false (by simp))
      apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$free_unions:clause:1» (head :: tail))
        n (.success (.of (unionsFree (head :: tail)))) n
      unfold SpecTec.«$free_unions:clause:1»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true (by simp)
      apply SpecTecExecution.Eval.bind_success ih
      apply SpecTecExecution.Eval.bind_success
        (free_union_total head (unionsFree tail) n)
      exact SpecTecExecution.Eval.pure _

theorem hasFunc_unionsFree (fs : List SpecTec.free)
    (f : SpecTec.free) (x : SpecTec.funcidx)
    (hf : f ∈ fs) (hfx : HasFunc f x) :
    HasFunc (unionsFree fs) x := by
  induction fs with
  | nil => cases hf
  | cons head tail ih =>
      rcases List.mem_cons.mp hf with h | h
      · subst f
        exact hasFunc_union head (unionsFree tail) x (.inl hfx)
      · exact hasFunc_union head (unionsFree tail) x
          (.inr (ih h))

theorem free_unions_preserves_funcs (fs : List SpecTec.free)
    (result f : SpecTec.free) (x : SpecTec.funcidx)
    (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.free, SpecTec.Call.«$free_unions» fs⟩)
      n (.success (.of result)) finalSupply)
    (hf : f ∈ fs) (hfx : HasFunc f x) : HasFunc result x := by
  obtain ⟨hout, _⟩ :=
    properties.wasm_module_ok.Execution.eval_deterministic hcall (free_unions_total fs n)
  cases hout
  exact hasFunc_unionsFree fs f x hf hfx

theorem fold_left_empty_total (a : SpecTec.free) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.free,
        SpecTec.Call.«$fold_left» SpecTec.free SpecTec.free
          SpecTec.Call.«$free_union» a []⟩)
      n (.success (.of a)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$fold_left_clauses» SpecTec.free SpecTec.free
        SpecTec.Call.«$free_union» a []))
    n (.success (.of a)) n
  apply SpecTecExecution.tryClauses_cons_success
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«$fold_left:clause:0» SpecTec.free SpecTec.free
      SpecTec.Call.«$free_union» a [])
    n (.success (.of a)) n
  unfold SpecTec.«$fold_left:clause:0»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true (by simp)
  exact SpecTecExecution.Eval.pure _

theorem fold_left_singleton_total (a b : SpecTec.free) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.free,
        SpecTec.Call.«$fold_left» SpecTec.free SpecTec.free
          SpecTec.Call.«$free_union» a [b]⟩)
      n (.success (.of (unionFree a b))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$fold_left_clauses» SpecTec.free SpecTec.free
        SpecTec.Call.«$free_union» a [b]))
    n (.success (.of (unionFree a b))) n
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$fold_left:clause:0» SpecTec.free SpecTec.free
        SpecTec.Call.«$free_union» a [b]) n .unmatch n
    unfold SpecTec.«$fold_left:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp))
  apply SpecTecExecution.tryClauses_cons_success
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«$fold_left:clause:1» SpecTec.free SpecTec.free
      SpecTec.Call.«$free_union» a [b])
    n (.success (.of (unionFree a b))) n
  unfold SpecTec.«$fold_left:clause:1»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true (by simp)
  apply SpecTecExecution.Eval.bind_success (free_union_total a b n)
  apply SpecTecExecution.Eval.bind_success
    (fold_left_empty_total (unionFree a b) n)
  exact SpecTecExecution.Eval.pure _

theorem free_instr_list_cons_success_iff
    (instr : SpecTec.instr) (rest : List SpecTec.instr)
    (result : SpecTec.free) (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.free,
        SpecTec.Call.«$free_list:specialized:627ab0672e3a767978c05fd35fc5a959»
          (instr :: rest)⟩)
      n (.success (.of result)) finalSupply ↔
    ∃ (headFree tailFree : SpecTec.free) (middle₁ middle₂ : Nat),
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.free, SpecTec.Call.«$free_instr» instr⟩)
        n (.success (.of headFree)) middle₁ ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.free,
          SpecTec.Call.«$free_list:specialized:627ab0672e3a767978c05fd35fc5a959» rest⟩)
        middle₁ (.success (.of tailFree)) middle₂ ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.free,
          SpecTec.Call.«$fold_left» SpecTec.free SpecTec.free
            SpecTec.Call.«$free_union» headFree [tailFree]⟩)
        middle₂ (.success (.of result)) finalSupply := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.Body
        (.orElse
          (SpecTec.«$free_list:specialized:627ab0672e3a767978c05fd35fc5a959:clause:0»
            (instr :: rest))
          (fun _ => SpecTecExecution.tryClauses
            [
              SpecTec.«$free_list:specialized:627ab0672e3a767978c05fd35fc5a959:clause:1»
                (instr :: rest)]))
        n (.success (.of result)) finalSupply at hbody
      cases hbody with
      | orElse_success hfirst =>
        unfold SpecTec.«$free_list:specialized:627ab0672e3a767978c05fd35fc5a959:clause:0» at hfirst
        cases hfirst with
        | bind_success hguard _ =>
          cases hguard with
          | guard_true hcond => simp at hcond
      | orElse_unmatch hfailedSupply htail =>
        restore_supply hfailedSupply at htail
        change SpecTecExecution.Eval SpecTec.Body
          (.orElse
            (SpecTec.«$free_list:specialized:627ab0672e3a767978c05fd35fc5a959:clause:1»
              (instr :: rest)) (fun _ => .unmatch))
          n (.success (.of result)) finalSupply at htail
        cases htail with
        | orElse_success hsecond =>
          unfold SpecTec.«$free_list:specialized:627ab0672e3a767978c05fd35fc5a959:clause:1» at hsecond
          cases hsecond with
          | bind_success hguard htail =>
            cases hguard with
            | guard_true _ =>
              cases htail with
              | bind_success hhead htail =>
                rename_i middle₁ headFree
                cases htail with
                | bind_success hrest htail =>
                  rename_i middle₂ tailFree
                  cases htail with
                  | bind_success hfold hpure =>
                    cases hpure with
                    | pure => exact ⟨headFree, tailFree,
                        middle₁, middle₂, hhead, hrest, hfold⟩
        | orElse_unmatch hfailedSupply hnone => restore_supply hfailedSupply at hnone; cases hnone
  · rintro ⟨headFree, tailFree, middle₁, middle₂,
      hhead, hrest, hfold⟩
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.«$free_list:specialized:627ab0672e3a767978c05fd35fc5a959_clauses»
          (instr :: rest)))
      n (.success (.of result)) finalSupply
    apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$free_list:specialized:627ab0672e3a767978c05fd35fc5a959:clause:0»
          (instr :: rest)) n .unmatch n
      unfold SpecTec.«$free_list:specialized:627ab0672e3a767978c05fd35fc5a959:clause:0»
      exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false (by simp))
    apply SpecTecExecution.tryClauses_cons_success
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_list:specialized:627ab0672e3a767978c05fd35fc5a959:clause:1»
        (instr :: rest)) n (.success (.of result)) finalSupply
    unfold SpecTec.«$free_list:specialized:627ab0672e3a767978c05fd35fc5a959:clause:1»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true (by simp)
    apply SpecTecExecution.Eval.bind_success hhead
    apply SpecTecExecution.Eval.bind_success hrest
    apply SpecTecExecution.Eval.bind_success hfold
    exact SpecTecExecution.Eval.pure _

theorem hasFunc_singleton (x : SpecTec.funcidx) :
    HasFunc (FreeRefsValidation.singletonFuncFree x) x := by
  simp [HasFunc, FreeRefsValidation.singletonFuncFree]

theorem free_instr_list_ref_func
    (xs : List SpecTec.instr) (x : SpecTec.funcidx)
    (result : SpecTec.free) (n finalSupply : Nat)
    (hmem : SpecTec.instr.«REF.FUNC» x ∈ xs)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.free,
        SpecTec.Call.«$free_list:specialized:627ab0672e3a767978c05fd35fc5a959» xs⟩)
      n (.success (.of result)) finalSupply) : HasFunc result x := by
  induction xs generalizing n finalSupply result with
  | nil => cases hmem
  | cons instr rest ih =>
      obtain ⟨headFree, tailFree, middle₁, middle₂,
        hhead, htail, hfold⟩ :=
        (free_instr_list_cons_success_iff instr rest result n finalSupply).mp hcall
      obtain ⟨hresult, _⟩ :=
        properties.wasm_module_ok.Execution.eval_deterministic hfold
          (fold_left_singleton_total headFree tailFree middle₂)
      have hpart : HasFunc headFree x ∨ HasFunc tailFree x := by
        rcases List.mem_cons.mp hmem with h | h
        · subst instr
          obtain ⟨hfree, _⟩ :=
            properties.wasm_module_ok.Execution.eval_deterministic hhead
              (FreeRefsValidation.ref_func_free_total x n)
          cases hfree
          exact .inl (hasFunc_singleton x)
        · exact .inr (ih tailFree middle₁ middle₂ h htail)
      cases hresult
      exact hasFunc_union headFree tailFree x hpart

end properties.wasm_module_ok.FreeUnionValidation
