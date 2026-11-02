import properties.wasm_module_ok.FuncLocalsStageGenerator
import properties.wasm_module_ok.FuncbodyTrace

set_option autoImplicit false

namespace properties.wasm_module_ok.LocalsTraversal

def validFor (c : SpecTec.context) :
    List SpecTec.typeidx → List (List SpecTec.«local») → Prop
  | [], [] => True
  | _ :: xs, ls :: rest =>
      LocalListValidation.allLocalsValid c ls = true ∧
        validFor c xs rest
  | _, _ => False

def generate (c : SpecTec.context) :
    List SpecTec.typeidx → Gen (List (List SpecTec.«local»))
  | [] => pure []
  | _ :: xs =>
      (FuncLocalsStageGenerator.localsCorrect c).val >>= fun ls =>
        generate c xs >>= fun rest =>
          pure (ls :: rest)

theorem support_iff
    (c : SpecTec.context) (xs : List SpecTec.typeidx)
    (payload : List (List SpecTec.«local»)) :
    Gen.support (generate c xs) payload ↔
      validFor c xs payload := by
  induction xs generalizing payload with
  | nil =>
      cases payload <;> simp [generate, validFor]
  | cons x xs ih =>
      cases payload with
      | nil =>
          simp [generate, validFor,
            Gen.Support.support_bind, Gen.Support.support_pure]
      | cons ls rest =>
          simp only [generate, validFor,
            Gen.Support.support_bind, Gen.Support.support_pure]
          constructor
          · rintro ⟨chosen, hchosen, tail, htail, hpure⟩
            cases hpure
            rw [(FuncLocalsStageGenerator.localsCorrect c).property]
              at hchosen
            exact ⟨hchosen, (ih rest).1 htail⟩
          · rintro ⟨hvalid, htail⟩
            refine ⟨ls, ?_, rest, (ih rest).2 htail, rfl⟩
            rw [(FuncLocalsStageGenerator.localsCorrect c).property]
            exact hvalid

theorem empty_payload_valid
    (c : SpecTec.context) (xs : List SpecTec.typeidx) :
    validFor c xs (xs.map fun _ => []) := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact ⟨rfl, ih⟩

theorem nonempty
    (c : SpecTec.context) (xs : List SpecTec.typeidx) :
    Gen.support (generate c xs) (xs.map fun _ => []) :=
  (support_iff c xs _).2 (empty_payload_valid c xs)

theorem validFor_of_all_valid
    (c : SpecTec.context) (fs : List SpecTec.func)
    (hall : ∀ f ∈ fs,
      LocalListValidation.allLocalsValid c f.LOCALS = true) :
    validFor c (fs.map (·.FTYPE)) (fs.map (·.LOCALS)) := by
  induction fs with
  | nil => trivial
  | cons f fs ih =>
      exact ⟨hall f (by simp),
        ih (fun g hg => hall g (by simp [hg]))⟩

theorem validated_bodies_have_valid_locals
    (c : SpecTec.context) (fs : List SpecTec.func)
    (n finalSupply : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Module_ok:rule:iter:2» c fs⟩)
      n (.success (.of ())) finalSupply) :
    ∀ f ∈ fs,
      LocalListValidation.allLocalsValid c f.LOCALS = true := by
  induction fs generalizing n finalSupply with
  | nil =>
      intro f hf
      cases hf
  | cons head tail ih =>
      obtain ⟨middle, hhead, htail⟩ :=
        (FunctionBodyValidation.funcbody_iter_cons_success_iff
          c head tail n finalSupply).1 h
      obtain ⟨args, results, htype, hlocals, hblock⟩ :=
        (FuncbodyTrace.funcbody_success_iff_precomputed
          c head n middle).1 hhead
      intro f hf
      rcases List.mem_cons.mp hf with heq | hmem
      · subst f
        exact hlocals
      · exact ih middle finalSupply htail f hmem

theorem supported_of_validated_bodies
    (c : SpecTec.context) (fs : List SpecTec.func)
    (n finalSupply : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Module_ok:rule:iter:2» c fs⟩)
      n (.success (.of ())) finalSupply) :
    Gen.support (generate c (fs.map (·.FTYPE)))
      (fs.map (·.LOCALS)) := by
  apply (support_iff c (fs.map (·.FTYPE))
    (fs.map (·.LOCALS))).2
  exact validFor_of_all_valid c fs
    (validated_bodies_have_valid_locals c fs n finalSupply h)

def stage : Staged.Stage
    (SpecTec.context × List SpecTec.typeidx)
    (List (List SpecTec.«local»)) where
  entry := fun _ => True
  nextEntry := fun _ => True
  valid := fun input payload => validFor input.1 input.2 payload
  generate := fun input => generate input.1 input.2
  always := by
    intro input _
    exact ⟨input.2.map (fun _ => []),
      empty_payload_valid input.1 input.2, trivial⟩
  sound := by
    intro input payload _ h
    exact ⟨(support_iff input.1 input.2 payload).1 h, trivial⟩
  complete := by
    intro input payload _ hv _
    exact (support_iff input.1 input.2 payload).2 hv

end properties.wasm_module_ok.LocalsTraversal
