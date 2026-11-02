import properties.wasm_module_ok.ConstructiveImportEntries
import properties.wasm_module_ok.ConstructiveNames
import properties.wasm_module_ok.ImportsValidation

set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveImports
open SpecTec properties.wasm_module_ok

structure Step (c : context) where
  item : SpecTec.«import»
  after : context
  correct : ImportValidation.importDeclResult c item = some after

def step (c : context) (e : ConstructiveImportEntries.Entry c) (m n : SpecTec.name) : Step c :=
  ⟨⟨m,n,e.descriptor⟩,e.output,e.correct m n⟩

def one (c : context) : Gen (Step c) := do
  let e ← (ConstructiveImportEntries.generate c).generator
  let modName ← ConstructiveNames.fresh []
  let itemName ← ConstructiveNames.fresh []
  pure (step c e modName itemName)

theorem one_audit (c : context) : ConstructiveGenAudit.Structural (one c) :=
  ⟨(ConstructiveImportEntries.generate c).audit,fun _ =>
    ⟨ConstructiveNames.fresh_audit [],fun _ => ⟨ConstructiveNames.fresh_audit [],fun _ => trivial⟩⟩⟩

theorem one_complete (c out : context) (i : SpecTec.«import»)
    (hi : ImportValidation.importDeclResult c i = some out) :
    ∃ s : Step c, Gen.support (one c) s ∧ s.item = i ∧ s.after = out := by
  obtain ⟨e,he,hd,ho⟩ := ConstructiveImportEntries.complete c out i hi
  refine ⟨step c e i.MODULENAME i.ITEMNAME,?_,?_,ho⟩
  · exact ⟨e,he,i.MODULENAME,(ConstructiveNames.fresh_exact [] _).2 (by simp),
      i.ITEMNAME,(ConstructiveNames.fresh_exact [] _).2 (by simp),rfl⟩
  · cases i; simp_all [step]

structure Result (c : context) where
  items : List SpecTec.«import»
  after : context
  correct : ImportsValidation.importsResult c items = some after

def done (c : context) : Result c := ⟨[],c,rfl⟩

def cons (c : context) (head : Step c) (tail : Result head.after) : Result c :=
  ⟨head.item::tail.items,tail.after,by
    simp only [ImportsValidation.importsResult,head.correct,Option.bind_some,tail.correct]⟩

def sized : Nat → (c : context) → Gen (Result c)
  | 0,c => pure (done c)
  | n+1,c => do
    let head ← one c
    let tail ← sized n head.after
    pure (cons c head tail)

def generate (c : context) : Gen (Result c) := Gen.arbNat >>= fun n => sized n c

def values (c : context) : Gen (List SpecTec.«import») := Result.items <$> generate c

theorem sized_audit (n : Nat) (c : context) : ConstructiveGenAudit.Structural (sized n c) := by
  induction n generalizing c with
  | zero => trivial
  | succ n ih => exact ⟨one_audit c,fun s => ⟨ih s.after,fun _ => trivial⟩⟩

theorem generate_audit (c : context) : ConstructiveGenAudit.Structural (generate c) :=
  ⟨ConstructiveGenAudit.arbNat_audit,fun n => sized_audit n c⟩

theorem sized_length (n : Nat) (c : context) (out : Result c) (h : Gen.support (sized n c) out) :
    out.items.length = n := by
  induction n generalizing c with
  | zero => have he : out = done c := h; subst out; rfl
  | succ n ih =>
    obtain ⟨head,_,tail,ht,rfl⟩ := h
    simpa [cons] using congrArg Nat.succ (ih head.after tail ht)

theorem sized_complete (c result : context) (items : List SpecTec.«import»)
    (h : ImportsValidation.importsResult c items = some result) :
    ∃ out : Result c, Gen.support (sized items.length c) out ∧ out.items = items ∧ out.after = result := by
  induction items generalizing c with
  | nil =>
    have he : c = result := Option.some.inj h
    exact ⟨done c,rfl,rfl,he⟩
  | cons i items ih =>
    cases hi : ImportValidation.importDeclResult c i with
    | none => simp [ImportsValidation.importsResult,hi] at h
    | some next =>
      have ht : ImportsValidation.importsResult next items = some result := by
        simpa [ImportsValidation.importsResult,hi] using h
      obtain ⟨head,hh,he,hout⟩ := one_complete c next i hi
      rw [← hout] at ht
      obtain ⟨tail,hg,hitems,hresult⟩ := ih head.after ht
      exact ⟨cons c head tail,⟨head,hh,tail,hg,rfl⟩,by simp [cons,he,hitems],hresult⟩

theorem generate_complete (c result : context) (items : List SpecTec.«import»)
    (h : ImportsValidation.importsResult c items = some result) :
    ∃ out : Result c, Gen.support (generate c) out ∧ out.items = items ∧ out.after = result := by
  obtain ⟨out,hg,hi,ho⟩ := sized_complete c result items h
  exact ⟨out,⟨items.length,by simp,hg⟩,hi,ho⟩

theorem execute (c : context) (out : Result c) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨context,SpecTec.Call.Imports_ok c out.items⟩) n (.success (.of out.after)) n :=
  (ImportsValidation.imports_success_iff_result c out.items out.after n n).2 ⟨out.correct,rfl⟩

/-- Exact original import-section support, all five descriptor kinds, all
names and arbitrary finite length. No assumptions on the incoming context. -/
theorem values_exact (c : context) (items : List SpecTec.«import») (n : Nat) :
    Gen.support (values c) items ↔ ∃ result : context,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨context,SpecTec.Call.Imports_ok c items⟩) n (.success (.of result)) n := by
  constructor
  · rintro ⟨out,_,rfl⟩; exact ⟨out.after,execute c out n⟩
  · rintro ⟨result,h⟩
    have hc := (ImportsValidation.imports_success_iff_result c items result n n).1 h |>.1
    obtain ⟨out,hg,hi,_⟩ := generate_complete c result items hc
    exact ⟨out,hg,hi.symm⟩

end properties.wasm_module_ok.ConstructiveImports
