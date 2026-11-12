import properties.wasm_module_ok.ConstructiveModuleEnvironment
import properties.wasm_module_ok.ConstructiveImportEntries
import properties.wasm_module_ok.FuncsValidation
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveModuleHeaders
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveImportTypes ConstructiveConstTableCore

def header (x : Nat) : SpecTec.func := ⟨x,[],[]⟩

structure Step (c : context) where
  item : SpecTec.func
  after : context
  env : Env after
  correct : FuncDeclValidation.funcDeclResult c item=some after

def step (c : context) (env : Env c) (i : FunctionIndex c) : Step c where
  item := ⟨i.val.val,[],[]⟩
  after := {c with FUNCS:=c.FUNCS++[c.TYPES[i.val.val]]}
  env := by
    apply ConstructiveModuleEnvironment.withFuncs c env _
    intro dt hm
    rcases List.mem_append.mp hm with hm|hm
    · exact env.provenance.funcs dt hm
    · have he : dt=c.TYPES[i.val.val] := by simpa using hm
      rw [he]; exact List.getElem_mem i.val.isLt
  correct := by
    cases he : UnrollInterface.deftypeFunctype c.TYPES[i.val.val] with
    | none => have hp := i.property; simp [he] at hp
    | some ft => simp [FuncDeclValidation.funcDeclResult,List.getElem?_eq_getElem i.val.isLt,he]

structure Result (c : context) where
  items : List SpecTec.func
  after : context
  env : Env after
  correct : FuncsValidation.funcsResult c items=some after

def done (c : context) (env : Env c) : Result c := ⟨[],c,env,rfl⟩
def cons (c : context) (head : Step c) (tail : Result head.after) : Result c :=
  ⟨head.item::tail.items,tail.after,tail.env,by
    simp only [FuncsValidation.funcsResult,head.correct,Option.bind_some,tail.correct]⟩

/-- Existing type metadata selects headers before any AST is constructed.
The empty branch completes even when no matching type is present. -/
def sized : Nat → (c : context) → Env c → Audited (Result c)
  | 0,c,env => Audited.pure (done c env)
  | n+1,c,env => (Audited.pure (done c env)).merge
      ((functions c).map fun i =>
        let head := step c env i
        (sized n head.after head.env).map (cons c head))

def generate (c : context) (env : Env c) : Gen (Result c) :=
  Gen.arbNat >>= fun n => (sized n c env).generator

theorem generate_audit (c : context) (env : Env c) : ConstructiveGenAudit.Structural (generate c env) :=
  ⟨ConstructiveGenAudit.arbNat_audit,fun n => (sized n c env).audit⟩

theorem execute (c : context) (out : Result c) (n : Nat) :
    SpecTecExecution.Eval Body (.call ⟨context,Call.Funcs_ok c out.items⟩)
      n (.success (.of out.after)) n :=
  (FuncsValidation.funcs_success_iff_result c out.items out.after n n).2 ⟨out.correct,rfl⟩

theorem step_complete (c out : context) (env : Env c) (item : SpecTec.func)
    (h : FuncDeclValidation.funcDeclResult c item=some out) :
    ∃i : FunctionIndex c,i∈functions c ∧
      let s := step c env i
      s.item = header item.FTYPE ∧ s.after=out := by
  rcases item with ⟨x,ls,body⟩
  cases hx : c.TYPES[x]? with
  | none => simp [FuncDeclValidation.funcDeclResult,hx] at h
  | some dt =>
      have hi := (List.getElem?_eq_some_iff.mp hx).1
      have hd := (List.getElem?_eq_some_iff.mp hx).2
      cases hf : UnrollInterface.deftypeFunctype dt with
      | none => simp [FuncDeclValidation.funcDeclResult,hx,hf] at h
      | some ft =>
        let i : FunctionIndex c := ⟨⟨x,hi⟩,by simp [hd,hf]⟩
        refine ⟨i,indices_cover c _ i.val i.property,rfl,?_⟩
        simpa [FuncDeclValidation.funcDeclResult,hx,hf,step,i,hd] using h

#print axioms execute
#print axioms step_complete

theorem sized_done (depth : Nat) (c : context) (env : Env c) :
    Gen.support (sized depth c env).generator (done c env) := by
  cases depth with
  | zero => rfl
  | succ n => exact (merge_support _ _ _).2 ⟨Audited.pure (done c env),by simp,rfl⟩

theorem sized_cons (depth : Nat) (c : context) (env : Env c) (i : FunctionIndex c)
    (hi : i∈functions c) (tail : Result (step c env i).after)
    (ht : Gen.support (sized depth (step c env i).after (step c env i).env).generator tail) :
    Gen.support (sized (depth+1) c env).generator (cons c (step c env i) tail) := by
  apply (merge_support _ _ _).2
  refine ⟨(sized depth (step c env i).after (step c env i).env).map (cons c (step c env i)),?_,?_⟩
  · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,hi,rfl⟩)
  · exact ⟨tail,ht,rfl⟩

theorem sized_complete (c result : context) (env : Env c) (xs : List Nat)
    (h : FuncsValidation.funcsResult c (xs.map header)=some result) :
    ∃out : Result c, Gen.support (sized xs.length c env).generator out ∧
      out.items=(xs.map header) ∧ out.after=result := by
  induction xs generalizing c with
  | nil =>
    have he : c=result := Option.some.inj h
    exact ⟨done c env,rfl,rfl,he⟩
  | cons x xs ih =>
    cases hh : FuncDeclValidation.funcDeclResult c (header x) with
    | none => simp [FuncsValidation.funcsResult,hh] at h
    | some next =>
      have ht : FuncsValidation.funcsResult next (xs.map header)=some result := by
        simpa only [List.map_cons,FuncsValidation.funcsResult,hh,Option.bind_some] using h
      obtain ⟨i,hi,he,ho⟩ := step_complete c next env (header x) hh
      rw [←ho] at ht
      obtain ⟨tail,hg,hxs,hout⟩ := ih (step c env i).after (step c env i).env ht
      refine ⟨cons c (step c env i) tail,sized_cons xs.length c env i hi tail hg,?_,hout⟩
      simp [cons,he,hxs,header]

theorem generate_complete (c result : context) (env : Env c) (xs : List Nat)
    (h : FuncsValidation.funcsResult c (xs.map header)=some result) :
    ∃out : Result c, Gen.support (generate c env) out ∧ out.items=(xs.map header) ∧ out.after=result := by
  obtain ⟨out,hg,hs,ho⟩ := sized_complete c result env xs h
  exact ⟨out,⟨xs.length,by simp,hg⟩,hs,ho⟩

#print axioms generate_complete
end properties.wasm_module_ok.ConstructiveModuleHeaders
