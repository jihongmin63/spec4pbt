import properties.wasm_module_ok.ConstructiveConstTargetExact
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveConstProductivePlans
open SpecTec properties.wasm_module_ok ConstructiveConstTree ConstructiveGenAudit
open properties.wasm_module_ok.ConstructiveConstBuilders properties.wasm_module_ok.ConstructiveConstAggregateBuilders
open properties.wasm_module_ok.ConstructiveConstTableCore properties.wasm_module_ok.ConstructiveConstTableSeeds properties.wasm_module_ok.ConstructiveConstTableExpand
open properties.wasm_module_ok.ConstructiveConstTableCoverage properties.wasm_module_ok.ConstructiveConstSeedCoverage properties.wasm_module_ok.ConstructiveConstGeneration
open properties.wasm_module_ok.ConstructiveConstTargetPlan properties.wasm_module_ok.ConstructiveConstTargetExact

abbrev Target (c : context) := {t : valtype // CandidateValMatch.InTableVal c t}
abbrev Productive (c : context) (hr : CandidateTypeReady.Ready c)
    (hp : CandidateUniverseReady.Provenance c) (hn : CandidateNestedReady.nestedTableReady c=true) :=
  (target : Target c) × Plan c hr hp hn target.val target.property

/-- A structural list of target type metadata; it contains no AST candidates. -/
def targetCatalog (c : context) (hp : CandidateUniverseReady.Provenance c)
    (hn : CandidateNestedReady.nestedTableReady c=true) : List (Target c) :=
  (ConstFieldCandidate.extendedCandidateTypes c).attach.map fun t =>
    ⟨t.val,ConstExtendedCandidateReady.extended_candidate_in_table c hp hn t.val
      (by simpa only [ConstFieldCandidate.extendedCandidateUniverse,List.mem_toFinset] using t.property)⟩

def plansFrom (c : context) (hr : CandidateTypeReady.Ready c)
    (hp : CandidateUniverseReady.Provenance c) (hn : CandidateNestedReady.nestedTableReady c=true)
    (catalog : List (Target c)) (n : Nat) : List (Productive c hr hp hn) :=
  catalog.flatMap fun target =>
    match planAt c hr hp hn target.val target.property n with
    | none => []
    | some plan => [⟨target,plan⟩]

def numericTarget (c : context) : Target c := ⟨.NumT .I32T,by intro ht h; cases h⟩

def numericPlan (c : context) (hr : CandidateTypeReady.Ready c)
    (hp : CandidateUniverseReady.Provenance c) (hn : CandidateNestedReady.nestedTableReady c=true) :
    Productive c hr hp hn := ⟨numericTarget c,⟨0,by
      let tree : Matched c (.NumT .I32T) := ⟨(number c (.I32 0)).val,(number c (.I32 0)).property.1,
        fun n => ConstNumericConsumer.match_numeric_singleton c .I32T n⟩
      have hc : Covers (rounds c hr hp hn 0) tree.val := by
        apply covers_mono ?_ (number_cover c hp (.I32 0))
        intro e he
        simp only [rounds,seeds,List.mem_append]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl he))))
      obtain ⟨g,hg,_⟩ := operand_cover c hr (.NumT .I32T) (numericTarget c).property _ tree hc
      exact ⟨g,hg⟩⟩⟩

/-- Choose a productive target before sampling its completed expression. -/
def productive (c : context) (hr : CandidateTypeReady.Ready c)
    (hp : CandidateUniverseReady.Provenance c) (hn : CandidateNestedReady.nestedTableReady c=true) :
    Gen (Productive c hr hp hn) := do
  let n ← Gen.arbNat
  ConstructiveTypeAtoms.choose (numericPlan c hr hp hn)
    (plansFrom c hr hp hn (targetCatalog c hp hn) n)

def pairedConstants (c : context) (hr : CandidateTypeReady.Ready c)
    (hp : CandidateUniverseReady.Provenance c) (hn : CandidateNestedReady.nestedTableReady c=true) :
    Gen (valtype × List instr) := do
  let plan ← productive c hr hp hn
  let code ← constants c hr hp hn plan.1.val plan.1.property plan.2
  pure (plan.1.val,code)

theorem productive_audit (c : context) (hr : CandidateTypeReady.Ready c)
    (hp : CandidateUniverseReady.Provenance c) (hn : CandidateNestedReady.nestedTableReady c=true) :
    Structural (productive c hr hp hn) := by
  refine ⟨arbNat_audit,fun n => finite_audit _ ?_⟩
  exact ConstructiveTypeAtoms.finite_choose _ _

theorem pairedConstants_audit (c : context) (hr : CandidateTypeReady.Ready c)
    (hp : CandidateUniverseReady.Provenance c) (hn : CandidateNestedReady.nestedTableReady c=true) :
    Structural (pairedConstants c hr hp hn) :=
  ⟨productive_audit c hr hp hn,fun p => ⟨constants_audit c hr hp hn p.1.val p.1.property p.2,fun _ => trivial⟩⟩

theorem pairedConstants_sound (c : context) (hr : CandidateTypeReady.Ready c)
    (hp : CandidateUniverseReady.Provenance c) (hn : CandidateNestedReady.nestedTableReady c=true)
    (target : valtype) (xs : List instr)
    (h : Gen.support (pairedConstants c hr hp hn) (target,xs)) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,SpecTecCall.Const_ok c target xs⟩) n (.success (.of ())) n := by
  obtain ⟨plan,hp,code,hc,he⟩ := h
  cases he
  exact constants_sound c hr _ hn _ _ plan.2 xs hc n

theorem targetCatalog_mem (c : context) (hp : CandidateUniverseReady.Provenance c)
    (hn : CandidateNestedReady.nestedTableReady c=true)
    (target : Target c) (ht : target.val∈ConstFieldCandidate.extendedCandidateUniverse c) :
    target∈targetCatalog c hp hn := by
  have ht' : target.val∈ConstFieldCandidate.extendedCandidateTypes c := by
    simpa only [ConstFieldCandidate.extendedCandidateUniverse,List.mem_toFinset] using ht
  exact List.mem_map.mpr ⟨⟨target.val,ht'⟩,by simp,Subtype.ext rfl⟩

theorem plansFrom_mem (c : context) (hr : CandidateTypeReady.Ready c)
    (hp : CandidateUniverseReady.Provenance c) (hn : CandidateNestedReady.nestedTableReady c=true)
    (catalog : List (Target c)) (target : Target c) (ht : target∈catalog) (n : Nat)
    (plan : Plan c hr hp hn target.val target.property)
    (h : planAt c hr hp hn target.val target.property n=some plan) :
    ⟨target,plan⟩∈plansFrom c hr hp hn catalog n := by
  exact List.mem_flatMap.mpr ⟨target,ht,by simp [h]⟩

theorem pairedConstants_complete (c : context) (hr : CandidateTypeReady.Ready c)
    (hp : CandidateUniverseReady.Provenance c) (hn : CandidateNestedReady.nestedTableReady c=true)
    (target : valtype) (ht : target∈ConstFieldCandidate.extendedCandidateUniverse c)
    (xs : List instr) (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,SpecTecCall.Const_ok c target xs⟩) start (.success (.of ())) finish) :
    Gen.support (pairedConstants c hr hp hn) (target,xs) := by
  let tgt : Target c := ⟨target,ConstExtendedCandidateReady.extended_candidate_in_table c hp hn target ht⟩
  obtain ⟨n,plan,hplan⟩ := original_has_plan c hr hp hn target tgt.property xs start finish h
  have hmem := plansFrom_mem c hr hp hn (targetCatalog c hp hn) tgt (targetCatalog_mem c hp hn tgt ht) n plan hplan
  have hpick : Gen.support (productive c hr hp hn) ⟨tgt,plan⟩ :=
    ⟨n,by simp,(ConstructiveTypeAtoms.support_choose _ _ _).2 (List.mem_cons_of_mem _ hmem)⟩
  exact ⟨⟨tgt,plan⟩,hpick,xs,constants_complete c hr hp hn target tgt.property plan xs start finish h,rfl⟩

theorem plansFrom_target_mem (c : context) (hr : CandidateTypeReady.Ready c)
    (hp : CandidateUniverseReady.Provenance c) (hn : CandidateNestedReady.nestedTableReady c=true)
    (catalog : List (Target c)) (n : Nat) (p : Productive c hr hp hn)
    (h : p∈plansFrom c hr hp hn catalog n) : p.1∈catalog := by
  obtain ⟨t,ht,hmem⟩ := List.mem_flatMap.mp h
  cases he : planAt c hr hp hn t.val t.property n with
  | none => simp [he] at hmem
  | some p' =>
    have hpeq : p=⟨t,p'⟩ := by simpa [he] using hmem
    subst p
    exact ht

theorem catalog_value (c : context) (hp : CandidateUniverseReady.Provenance c)
    (hn : CandidateNestedReady.nestedTableReady c=true)
    (t : Target c) (h : t∈targetCatalog c hp hn) :
    t.val∈ConstFieldCandidate.extendedCandidateUniverse c := by
  obtain ⟨u,hu,he⟩ := List.mem_map.mp h
  have hv : u.val=t.val := congrArg Subtype.val he
  simpa only [ConstFieldCandidate.extendedCandidateUniverse,List.mem_toFinset,hv] using u.property

theorem productive_target (c : context) (hr : CandidateTypeReady.Ready c)
    (hp : CandidateUniverseReady.Provenance c) (hn : CandidateNestedReady.nestedTableReady c=true)
    (p : Productive c hr hp hn) (h : Gen.support (productive c hr hp hn) p) :
    p.1.val∈ConstFieldCandidate.extendedCandidateUniverse c := by
  obtain ⟨n,_,hchoice⟩ := h
  rcases List.mem_cons.mp ((ConstructiveTypeAtoms.support_choose _ _ _).1 hchoice) with rfl|hmem
  · exact ConstFieldCandidate.old_candidate_mem_extended c _
      (FiniteValidTypes.valid_mem_candidateUniverse c _ (by rfl))
  · exact catalog_value c hp hn p.1 (plansFrom_target_mem c hr hp hn _ n p hmem)

theorem pairedConstants_exact (c : context) (hr : CandidateTypeReady.Ready c)
    (hp : CandidateUniverseReady.Provenance c) (hn : CandidateNestedReady.nestedTableReady c=true)
    (target : valtype) (xs : List instr) (n : Nat) :
    Gen.support (pairedConstants c hr hp hn) (target,xs) ↔
      target∈ConstFieldCandidate.extendedCandidateUniverse c ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit,SpecTecCall.Const_ok c target xs⟩) n (.success (.of ())) n := by
  constructor
  · intro h
    refine ⟨?_,pairedConstants_sound c hr hp hn target xs h n⟩
    obtain ⟨p,hp',code,hc,he⟩ := h
    cases he
    exact productive_target c hr hp hn p hp'
  · rintro ⟨ht,h⟩
    exact pairedConstants_complete c hr hp hn target ht xs n n h

#print axioms pairedConstants_audit
#print axioms pairedConstants_sound
#print axioms pairedConstants_complete
end properties.wasm_module_ok.ConstructiveConstProductivePlans
