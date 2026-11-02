import properties.wasm_module_ok.ConstructiveGenAudit
import properties.wasm_module_ok.MemtypeValidation

set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveLimits
open SpecTec properties.wasm_module_ok

/-- The previously verified W04 balanced construction, retained as a reusable
property component. Recursion is inside the chosen continuation, so a 64-bit
bound needs only logarithmic sampling depth and never enumerates the range. -/
def bounded (bound : Nat) : Gen Nat :=
  if bound = 0 then pure 0
  else do
    let right ← Gen.pick (pure false) (pure true)
    if right then
      (fun n => (bound+1)/2+n) <$> bounded (bound-(bound+1)/2)
    else bounded ((bound+1)/2-1)
termination_by bound
decreasing_by all_goals omega

theorem bounded_support (bound value : Nat) : Gen.support (bounded bound) value ↔ value ≤ bound := by
  induction bound using Nat.strongRecOn generalizing value with
  | ind bound ih =>
    rw [bounded]
    split
    · rename_i hz; subst bound; simp
    · rename_i hn
      have hl : (bound+1)/2-1 < bound := by omega
      have hr : bound-(bound+1)/2 < bound := by omega
      simp only [Gen.Support.support_bind,Gen.Support.support_pick,Gen.Support.support_pure]
      constructor
      · rintro ⟨side,_,hv⟩
        cases side <;> simp only [Bool.false_eq_true,ite_false,ite_true,
          Gen.Support.support_map,ih _ hl,ih _ hr] at hv
        · omega
        · obtain ⟨n,hn,heq⟩ := hv; omega
      · intro hv
        by_cases hlow : value < (bound+1)/2
        · refine ⟨false,Or.inl rfl,?_⟩
          simp only [Bool.false_eq_true,ite_false,ih _ hl]
          omega
        · refine ⟨true,Or.inr rfl,?_⟩
          simp only [ite_true,Gen.Support.support_map,ih _ hr]
          exact ⟨value-(bound+1)/2,by omega,by omega⟩

theorem bounded_finite (bound : Nat) : ConstructiveTypeAtoms.FiniteConstruction (bounded bound) := by
  induction bound using Nat.strongRecOn with
  | ind bound ih =>
    rw [bounded]
    split
    · trivial
    · rename_i hn
      refine ⟨⟨trivial,trivial⟩,?_⟩
      intro side
      cases side
      · exact ih _ (by omega)
      · exact ⟨ih _ (by omega),fun _ => trivial⟩

def limits (bound : Nat) : Gen SpecTec.limits := do
  let lower ← bounded bound
  Gen.pick (pure ⟨lower,none⟩) (do
    let slack ← bounded (bound-lower)
    pure ⟨lower,some (lower+slack)⟩)

theorem limits_support (bound : Nat) (lim : SpecTec.limits) :
    Gen.support (limits bound) lim ↔ LimitsValidation.limitsValid bound lim = true := by
  rcases lim with ⟨lower,upper⟩
  change Nat at lower
  change Option Nat at upper
  simp only [limits,Gen.Support.support_bind,Gen.Support.support_pick,Gen.Support.support_pure]
  cases upper with
  | none => simp [bounded_support,LimitsValidation.limitsValid]
  | some upper =>
    simp only [LimitsValidation.limitsValid,decide_eq_true_eq,bounded_support,
      SpecTec.limits.mk.injEq,Option.some.injEq,reduceCtorEq,and_false,false_or]
    constructor
    · rintro ⟨lo,hlo,slack,hs,heq,hu⟩
      subst lo
      change lower ≤ bound ∧ upper ≤ bound ∧ lower ≤ upper
      exact ⟨hlo,by omega,by omega⟩
    · intro h
      change lower ≤ bound ∧ upper ≤ bound ∧ lower ≤ upper at h
      obtain ⟨hlo,hhi,horder⟩ := h
      exact ⟨lower,hlo,upper-lower,by omega,rfl,by omega⟩

theorem limits_finite (bound : Nat) : ConstructiveTypeAtoms.FiniteConstruction (limits bound) :=
  ⟨bounded_finite bound,fun lower => ⟨trivial,bounded_finite (bound-lower),fun _ => trivial⟩⟩

theorem limits_exact (c : context) (bound : Nat) (lim : SpecTec.limits) (start finish : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,SpecTec.Call.Limits_ok c bound lim⟩) start (.success (.of ())) finish ↔
      Gen.support (limits bound) lim ∧ finish = start := by
  rw [LimitsValidation.limits_success_iff_valid,limits_support]

def memories : Gen memtype := Gen.pick
  (memtype.MemoryT .I32AT <$> limits 65536)
  (memtype.MemoryT .I64AT <$> limits 281474976710656)

theorem memories_support (mt : memtype) :
    Gen.support memories mt ↔ MemtypeValidation.memtypeValid mt = true := by
  cases mt with
  | MemoryT addr lim =>
    cases addr <;> simp [memories,limits_support,MemtypeValidation.memtypeValid]

theorem memories_finite : ConstructiveTypeAtoms.FiniteConstruction memories :=
  ⟨⟨limits_finite _,fun _ => trivial⟩,⟨limits_finite _,fun _ => trivial⟩⟩

theorem memories_exact (c : context) (mt : memtype) (start finish : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,SpecTec.Call.Memtype_ok c mt⟩) start (.success (.of ())) finish ↔
      Gen.support memories mt ∧ finish = start := by
  rw [MemtypeValidation.memtype_success_iff_valid,memories_support]

end properties.wasm_module_ok.ConstructiveLimits
