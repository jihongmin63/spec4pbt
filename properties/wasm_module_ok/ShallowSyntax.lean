import properties.wasm_module_ok.RefCyclePrestage

set_option autoImplicit false

namespace properties.wasm_module_ok.ShallowSyntax

def shallowInstr : SpecTec.instr → Bool
  | .BLOCK _ _ => false
  | .LOOP _ _ => false
  | .«IF % % ELSE %» _ _ _ => false
  | .TRY_TABLE _ _ _ => false
  | _ => true

def shallowList (xs : List SpecTec.instr) : Bool :=
  xs.all shallowInstr

theorem shallow_false_nested (i : SpecTec.instr)
    (h : shallowInstr i = false) :
    ConstNestedValidation.Nested i := by
  cases i <;> simp [shallowInstr] at h
  all_goals first
    | exact .block _ _
    | exact .loop _ _
    | exact .if_ _ _ _
    | exact .tryTable _ _ _

theorem shallow_instr_iff_not_nested (i : SpecTec.instr) :
    shallowInstr i = true ↔ ¬ ConstNestedValidation.Nested i := by
  constructor
  · intro h hnested
    cases hnested <;> simp [shallowInstr] at h
  · intro h
    cases hv : shallowInstr i with
    | true => rfl
    | false => exact (h (shallow_false_nested i hv)).elim

theorem shallow_list_iff (xs : List SpecTec.instr) :
    shallowList xs = true ↔
      ∀ i ∈ xs, ¬ ConstNestedValidation.Nested i := by
  induction xs with
  | nil => simp [shallowList]
  | cons head rest ih =>
      simp [shallowList, shallow_instr_iff_not_nested, List.mem_cons]

theorem const_ok_shallow_list
    (c : SpecTec.context) (t : SpecTec.valtype)
    (xs : SpecTec.const) (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Const_ok c t xs⟩)
      n (.success (.of ())) finalSupply) :
    shallowList xs = true :=
  (shallow_list_iff xs).2
    (fun i hmem => ConstNestedValidation.const_ok_no_nested
      c t xs n finalSupply hcall i hmem)

theorem ref_occurs_direct_of_shallow
    (xs : List SpecTec.instr) (i : SpecTec.instr)
    (x : SpecTec.funcidx)
    (hshallow : shallowList xs = true)
    (hmem : i ∈ xs)
    (hocc : ConstNestedValidation.RefOccurs i x) :
    SpecTec.instr.«REF.FUNC» x ∈ xs := by
  have hnone := (shallow_list_iff xs).1 hshallow
  cases hocc with
  | direct x => exact hmem
  | block bt body j x _ _ =>
      exact ((hnone _ hmem) (.block bt body)).elim
  | loop bt body j x _ _ =>
      exact ((hnone _ hmem) (.loop bt body)).elim
  | ifYes bt yes no j x _ _ =>
      exact ((hnone _ hmem) (.if_ bt yes no)).elim
  | ifNo bt yes no j x _ _ =>
      exact ((hnone _ hmem) (.if_ bt yes no)).elim
  | tryTable bt catches body j x _ _ =>
      exact ((hnone _ hmem) (.tryTable bt catches body)).elim

inductive Occurs (m : SpecTec.module) : SpecTec.funcidx → Prop where
  | table (t : SpecTec.table) (i : SpecTec.instr)
      (x : SpecTec.funcidx) (ht : t ∈ m.TABLES)
      (hshallow : shallowList t.TINIT = true)
      (hi : i ∈ t.TINIT)
      (hocc : ConstNestedValidation.RefOccurs i x) : Occurs m x
  | global (g : SpecTec.global) (i : SpecTec.instr)
      (x : SpecTec.funcidx) (hg : g ∈ m.GLOBALS)
      (hshallow : shallowList g.GINIT = true)
      (hi : i ∈ g.GINIT)
      (hocc : ConstNestedValidation.RefOccurs i x) : Occurs m x
  | elemInit (e : SpecTec.elem) (init : SpecTec.const)
      (i : SpecTec.instr) (x : SpecTec.funcidx)
      (he : e ∈ m.ELEMS) (hinit : init ∈ e.EINIT)
      (hshallow : shallowList init = true)
      (hi : i ∈ init)
      (hocc : ConstNestedValidation.RefOccurs i x) : Occurs m x
  | elemOffset (e : SpecTec.elem) (a : SpecTec.active)
      (i : SpecTec.instr) (x : SpecTec.funcidx)
      (he : e ∈ m.ELEMS) (hmode : e.EMODE = .Active a)
      (hshallow : shallowList a.OFFSET = true)
      (hi : i ∈ a.OFFSET)
      (hocc : ConstNestedValidation.RefOccurs i x) : Occurs m x
  | dataOffset (d : SpecTec.data) (a : SpecTec.active)
      (i : SpecTec.instr) (x : SpecTec.funcidx)
      (hd : d ∈ m.DATAS) (hmode : d.DMODE = .Active a)
      (hshallow : shallowList a.OFFSET = true)
      (hi : i ∈ a.OFFSET)
      (hocc : ConstNestedValidation.RefOccurs i x) : Occurs m x

theorem occurs_direct
    (m : SpecTec.module) (x : SpecTec.funcidx)
    (h : Occurs m x) : RefCyclePrestage.DirectSyntax m x := by
  cases h with
  | table t i x ht hshallow hi hocc =>
      exact .table t x ht
        (ref_occurs_direct_of_shallow t.TINIT i x hshallow hi hocc)
  | global g i x hg hshallow hi hocc =>
      exact .global g x hg
        (ref_occurs_direct_of_shallow g.GINIT i x hshallow hi hocc)
  | elemInit e init i x he hinit hshallow hi hocc =>
      exact .elemInit e init x he hinit
        (ref_occurs_direct_of_shallow init i x hshallow hi hocc)
  | elemOffset e a i x he hmode hshallow hi hocc =>
      exact .elemOffset e a x he hmode
        (ref_occurs_direct_of_shallow a.OFFSET i x hshallow hi hocc)
  | dataOffset d a i x hd hmode hshallow hi hocc =>
      exact .dataOffset d a x hd hmode
        (ref_occurs_direct_of_shallow a.OFFSET i x hshallow hi hocc)

theorem instr_ok_iff_bound
    (m : SpecTec.module) (free : SpecTec.free)
    (nfree : Nat)
    (hfree : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.free, SpecTec.SpecTecCall.«$free_module»
        ({{m with FUNCS := []} with START := none})⟩)
      0 (.success (.of free)) nfree)
    (c : SpecTec.context) (hrefs : c.REFS = free)
    (x : SpecTec.funcidx) (hocc : Occurs m x)
    (irt : SpecTec.inferresulttype) (n : Nat) :
    (∃ (result : SpecTec.inferinstrtype) (finalSupply : Nat),
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.inferinstrtype,
          SpecTec.SpecTecCall.Instr_ok c irt (.«REF.FUNC» x)⟩)
        n (.success (.of result)) finalSupply) ↔
      x < c.FUNCS.length :=
  RefCyclePrestage.direct_instr_ok_iff_bound
    m free nfree hfree c hrefs x (occurs_direct m x hocc) irt n

end properties.wasm_module_ok.ShallowSyntax
