import properties.wasm_module_ok.RefCyclePrestage
import properties.wasm_module_ok.ConstInstrDecision
import properties.wasm_module_ok.ConstSyntaxCandidate
import properties.wasm_module_ok.ConstExactSyntaxBoundary
import properties.wasm_module_ok.PopMatchExtraction
import properties.wasm_module_ok.LocalInitValidation
import properties.wasm_module_ok.PushValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveRefs
open properties.wasm_module_ok

/-- Only the type table influences successful result matching. -/
theorem match_resulttype_transport (c d : SpecTec.context)
    (htypes : c.TYPES = d.TYPES) (a b : List SpecTec.valtype)
    (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Match_resulttype c a b⟩)
      start (.success (.of ())) finish) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Match_resulttype d a b⟩)
      start (.success (.of ())) finish := by
  obtain ⟨hlen, hiter⟩ :=
    (MatchResulttypeValidation.match_resulttype_success_iff c a b start finish).1 h
  apply (MatchResulttypeValidation.match_resulttype_success_iff d a b start finish).2
  refine ⟨hlen, ?_⟩
  clear h
  induction a generalizing b start with
  | nil =>
    cases b with
    | cons _ _ => simp at hlen
    | nil =>
      have hfin := (properties.wasm_module_ok.Execution.eval_deterministic hiter
        (MatchResulttypeValidation.match_iter_nil_total c start)).2
      subst finish
      exact MatchResulttypeValidation.match_iter_nil_total d start
  | cons a as ih =>
    cases b with
    | nil => simp at hlen
    | cons b bs =>
      obtain ⟨middle, hhead, htail⟩ :=
        (MatchResulttypeValidation.match_iter_cons_success_iff c a b as bs start finish).1 hiter
      apply (MatchResulttypeValidation.match_iter_cons_success_iff d a b as bs start finish).2
      exact ⟨middle, by simpa only [htypes] using hhead,
        ih bs middle (by simpa using hlen) htail⟩

/-- Retain the input counter in the exact pop-to-match bridge. -/
theorem pop_match_exact (c : SpecTec.context)
    (need available : List SpecTec.valtype)
    (result : SpecTec.inferresulttype) (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferresulttype, SpecTec.Call.«$pop» c
        (.NoEllipses, need) (.NoEllipses, available)⟩)
      start (.success (.of result)) finish) :
    need.length ≤ available.length ∧
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Match_resulttype c
        (available.drop (available.length - need.length)) need⟩)
      start (.success (.of ())) finish := by
  have hlen := PopLength.pop_noellipses_success_requires_length
    c need available result start finish h
  refine ⟨hlen, ?_⟩
  cases h with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.«$pop_clauses» c
          (.NoEllipses, need) (.NoEllipses, available)))
      start (.success (.of result)) finish at hbody
    obtain ⟨idx, hselected⟩ :=
      (SpecTecExecution.tryClauses_success_iff
        (SpecTec.«$pop_clauses» c
          (.NoEllipses, need) (.NoEllipses, available))
        start (.of result) finish).1 hbody
    unfold SpecTec.«$pop_clauses» at hselected
    cases hselected with
    | here h0 =>
      unfold SpecTec.«$pop:clause:0» at h0
      cases h0 with
      | bind_success hguard _ =>
        cases hguard with
        | guard_true hg => simp [SpecTec.«exec:match:ellipses:Ellipses»] at hg
    | next _ hselected =>
      cases hselected with
      | here h1 =>
        unfold SpecTec.«$pop:clause:1» at h1
        cases h1 with
        | bind_success _ htail =>
          cases htail with
          | bind_success hguard _ =>
            cases hguard with
            | guard_true hg => simp [SpecTec.«exec:match:ellipses:Ellipses»] at hg
      | next _ hselected =>
        cases hselected with
        | here h2 =>
          unfold SpecTec.«$pop:clause:2» at h2
          cases h2 with
          | bind_success hguard _ =>
            cases hguard with
            | guard_true hg => simp [SpecTec.«exec:match:ellipses:Ellipses»] at hg
        | next _ hselected =>
          cases hselected with
          | here h3 =>
            unfold SpecTec.«$pop:clause:3» at h3
            cases h3 with
            | bind_success hguard0 htail =>
              cases hguard0
              cases htail with
              | bind_success hguard1 htail =>
                cases hguard1
                cases htail with
                | bind_success hmin htail =>
                  have hminval := (MinValidation.min_success_iff
                    need.length available.length _ _ _).1 hmin
                  rcases hminval with ⟨rfl, rfl⟩
                  have hdiff :
                      Int.ofNat available.length - Int.ofNat
                        (min need.length available.length) =
                        Int.ofNat (available.length -
                          min need.length available.length) :=
                    (Int.ofNat_sub (Nat.min_le_right _ _)).symm
                  simp only [hdiff, Int.toNat?] at htail
                  simp [Nat.min_eq_left hlen] at htail
                  cases htail with
                  | bind_success hguard2 htail =>
                    cases hguard2
                    simp at htail
                    cases htail with
                    | bind_success hrequire0 htail =>
                      have hb : available.length - need.length + need.length ≤ available.length := by omega
                      have hcounter := (properties.wasm_module_ok.Execution.eval_deterministic hrequire0
                        (SpecTecExecution.Eval.orElse_success
                          (SpecTecExecution.Eval.guard_true hb))).2
                      cases hcounter
                      cases htail with
                      | bind_success hmatch htail =>
                        rename_i matchStart matchValue
                        have htailLength :
                            (available.drop (available.length - need.length)).length =
                              need.length := by
                          simp [List.length_drop]
                          omega
                        have htake :
                            (available.drop (available.length - need.length)).take
                                need.length =
                              available.drop (available.length - need.length) :=
                          List.take_of_length_le (by omega)
                        rw [htake] at hmatch
                        cases htail with
                        | bind_success hrequire hpure =>
                          cases hpure
                          cases matchValue
                          unfold SpecTecExecution.require at hrequire
                          cases hrequire with
                          | orElse_success hguard =>
                            cases hguard with
                            | guard_true _ => exact hmatch
                          | orElse_unmatch hguard _ =>
                            cases hguard with
                            | guard_false hfalse => simp at hfalse
          | next _ hnone => cases hnone



theorem pop_transport (c d : SpecTec.context) (htypes : c.TYPES = d.TYPES)
    (need available : List SpecTec.valtype) (result : SpecTec.inferresulttype)
    (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferresulttype, SpecTec.Call.«$pop» c
        (.NoEllipses, need) (.NoEllipses, available)⟩)
      start (.success (.of result)) finish) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferresulttype, SpecTec.Call.«$pop» d
        (.NoEllipses, need) (.NoEllipses, available)⟩)
      start (.success (.of result)) finish := by
  obtain ⟨hlen, hm⟩ := pop_match_exact c need available result start finish h
  have hr := PopResult.pop_noellipses_success_result c need available result start finish h
  rw [hr]
  exact PopGeneralValidation.pop_noellipses_of_match d need available start finish hlen
    (match_resulttype_transport c d htypes _ _ start finish hm)

@[simp] theorem syntax_replace_refs (c : SpecTec.context) (refs : SpecTec.free)
    (i : SpecTec.instr) :
    ConstSyntaxDecision.syntaxAllowed {c with REFS := refs} i =
      ConstSyntaxDecision.syntaxAllowed c i := rfl

/-- No new instruction is selected here: transport retains exact original syntax. -/
theorem instruction_result_replace_refs
    (c : SpecTec.context) (refs : SpecTec.free) (stack : SpecTec.inferresulttype)
    (i : SpecTec.instr) (iit : SpecTec.inferinstrtype)
    (hrefs : ∀ x, i = SpecTec.instr.«REF.FUNC» x → FreeUnionValidation.HasFunc refs x)
    (h : ConstInstrDecision.constantInstructionResult c stack i = some iit) :
    ConstInstrDecision.constantInstructionResult {c with REFS := refs} stack i = some iit := by
  cases i <;> try exact h
  case «REF.FUNC» x =>
    have hallowed : ConstInstrDecision.refFuncAllowed {c with REFS := refs} x = true :=
      (ConstInstrDecision.ref_func_allowed_iff _ _).2 (hrefs x rfl)
    simp only [ConstInstrDecision.constantInstructionResult,
      ConstSyntaxDecision.syntaxAllowed, ConstArithmeticValidation.arithmeticOps,
      List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq,
      if_false, if_true, ConstInstrDecision.refFuncResult] at h ⊢
    cases hg : c.FUNCS[x]? with
    | none => simp [hg] at h
    | some dt =>
      have hv := (by simpa [hg] using h :
        ConstInstrDecision.refFuncAllowed c x = true ∧
        (({ INS := (.NoEllipses, []),
            OUTS := (.NoEllipses, [.RefT (.«% %» .NoNull (.DefHT dt))])
          } : SpecTec.inferfunctype), ([] : List SpecTec.localidx)) = iit)
      simpa [hg, hallowed] using hv.2
  case «STRUCT.NEW» x op => cases op <;> exact h
  case «ARRAY.NEW» x op => cases op <;> exact h


/-- Every exact constant sequence can be replayed with any occurrence-realizing
reference set. All instruction forms and both supply endpoints are retained. -/
theorem const_instrs_replace_refs (c : SpecTec.context) (refs : SpecTec.free)
    (xs : List SpecTec.instr) (available : List SpecTec.valtype)
    (result : SpecTec.inferresulttype × List SpecTec.idx) (start finish : Nat)
    (hsyntax : ∀ i ∈ xs, ConstAdditionalSyntaxValidation.Syntax c i)
    (hrefs : ∀ x, SpecTec.instr.«REF.FUNC» x ∈ xs → FreeUnionValidation.HasFunc refs x)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferresulttype × List SpecTec.idx,
        SpecTec.Call.Instrs_ok c (.NoEllipses, available) xs⟩)
      start (.success (.of result)) finish) :
    result.1.1 = .NoEllipses ∧
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferresulttype × List SpecTec.idx,
        SpecTec.Call.Instrs_ok {c with REFS := refs} (.NoEllipses, available) xs⟩)
      start (.success (.of result)) finish := by
  induction xs generalizing available start with
  | nil =>
    obtain ⟨heq, hfin⟩ := (InstrsValidation.instrs_nil_success_iff
      c (.NoEllipses, available) result start finish).1 h
    subst result
    subst finish
    exact ⟨rfl, InstrsValidation.instrs_nil_total _ _ _⟩
  | cons i rest ih =>
    obtain ⟨iit, next, popped, pushed, n1, n2, n3, n4, hi, hl, hp, hpush, hrest⟩ :=
      (InstrsValidation.instrs_cons_success_iff
        c (.NoEllipses, available) i rest result start finish).1 h
    have hsi := hsyntax i (by simp)
    have hallowed := (ConstSyntaxDecision.syntaxAllowed_iff c i).2 hsi
    obtain ⟨hr, hcounter⟩ :=
      (ConstInstrDecision.constant_instruction_result_iff c (.NoEllipses, available)
        i iit start n1).2 ⟨hallowed, hi⟩
    have hnew := instruction_result_replace_refs c refs (.NoEllipses, available) i iit
      (by intro x hx; apply hrefs x; simp [hx]) hr
    have hinew := ((ConstInstrDecision.constant_instruction_result_iff
      {c with REFS := refs} (.NoEllipses, available) i iit start n1).1
      ⟨hnew, hcounter⟩).2
    obtain ⟨need, hins, hlocals⟩ :=
      ConstInstrDecision.syntax_instruction_input_shape c (.NoEllipses, available)
        i iit start n1 hsi hi
    obtain ⟨_, outs, _, houts, _⟩ :=
      ConstSyntaxCandidate.syntax_instruction_effect_candidate c c i
        (.NoEllipses, available) iit start n1 hsi hi
    obtain ⟨hlr, hlcounter⟩ :=
      (LocalInitValidation.init_locals_success_iff_result c iit.2 next n1 n2).1 hl
    have hnext : next = c := by
      simpa only [hlocals, LocalInitValidation.initLocalsResult, Option.some.injEq]
        using hlr.symm
    subst next
    subst n2
    have hpop := hp
    rw [hins] at hpop
    have hpe := PopResult.pop_noellipses_success_result c need available popped n1 n3 hpop
    have hnewpop := pop_transport c {c with REFS := refs} rfl
      need available popped n1 n3 hpop
    have hpushparts := (PushValidation.push_success_iff_result
      c iit.1.OUTS popped pushed n3 n4).1 hpush
    have hpushshape : pushed = (.NoEllipses,
        available.take (available.length - need.length) ++ outs) := by
      simpa only [houts, hpe, PushValidation.pushResult, Option.some.injEq]
        using hpushparts.1.symm
    have hnewpush := (PushValidation.push_success_iff_result
      {c with REFS := refs} iit.1.OUTS popped pushed n3 n4).2 hpushparts
    rw [hpushshape] at hrest
    obtain ⟨hshape, hnewrest⟩ := ih _ n4
      (fun j hj => hsyntax j (by simp [hj]))
      (fun x hx => hrefs x (by simp [hx])) hrest
    refine ⟨hshape, (InstrsValidation.instrs_cons_success_iff
      {c with REFS := refs} (.NoEllipses, available) i rest result start finish).2 ?_⟩
    refine ⟨iit, {c with REFS := refs}, popped, pushed, n1, n1, n3, n4,
      hinew, ?_, ?_, hnewpush, ?_⟩
    · simpa only [hlocals] using LocalInitValidation.init_locals_nil_total
        {c with REFS := refs} n1
    · simpa only [hins] using hnewpop
    · simpa only [hpushshape] using hnewrest

/-- Exact constants are portable to their final syntax-derived REFS. No
ModuleOkTrace, readiness, provenance, or productive-saturation premise. -/
theorem const_ok_replace_refs (c : SpecTec.context) (refs : SpecTec.free)
    (t : SpecTec.valtype) (xs : SpecTec.const) (start finish : Nat)
    (hrefs : ∀ x, SpecTec.instr.«REF.FUNC» x ∈ xs → FreeUnionValidation.HasFunc refs x)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Const_ok c t xs⟩)
      start (.success (.of ())) finish) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Const_ok {c with REFS := refs} t xs⟩)
      start (.success (.of ())) finish := by
  obtain ⟨hsyntax, stack, indices, ell, middle, hseq, hpop⟩ :=
    (ConstExactSyntaxBoundary.const_ok_trace_iff c t xs start finish).1 h
  obtain ⟨hshape, hnewseq⟩ := const_instrs_replace_refs c refs xs []
    (stack, indices) start middle hsyntax hrefs hseq
  have hnewsyntax : ∀ i ∈ xs, ConstAdditionalSyntaxValidation.Syntax {c with REFS := refs} i := by
    intro i hi
    apply (ConstSyntaxDecision.syntaxAllowed_iff _ _).1
    rw [syntax_replace_refs]
    exact (ConstSyntaxDecision.syntaxAllowed_iff _ _).2 (hsyntax i hi)
  rcases stack with ⟨dots, ts⟩
  change dots = .NoEllipses at hshape
  subst dots
  have hnewpop := pop_transport c {c with REFS := refs} rfl [t] ts
    (ell, []) middle finish hpop
  exact (ConstExactSyntaxBoundary.const_ok_trace_iff
    {c with REFS := refs} t xs start finish).2
    ⟨hnewsyntax, (.NoEllipses, ts), indices, ell, middle, hnewseq, hnewpop⟩


/-- An actual constant-expression field, retaining its original module location. -/
inductive InitializerSite (m : SpecTec.module) : SpecTec.const → Prop where
  | table (t : SpecTec.table) (h : t ∈ m.TABLES) : InitializerSite m t.TINIT
  | global (g : SpecTec.global) (h : g ∈ m.GLOBALS) : InitializerSite m g.GINIT
  | elemInit (e : SpecTec.elem) (xs : SpecTec.const)
      (h : e ∈ m.ELEMS) (hx : xs ∈ e.EINIT) : InitializerSite m xs
  | elemOffset (e : SpecTec.elem) (a : SpecTec.active)
      (h : e ∈ m.ELEMS) (ha : e.EMODE = .Active a) : InitializerSite m a.OFFSET
  | dataOffset (d : SpecTec.data) (a : SpecTec.active)
      (h : d ∈ m.DATAS) (ha : d.DMODE = .Active a) : InitializerSite m a.OFFSET

theorem initializer_direct (m : SpecTec.module) (xs : SpecTec.const)
    (hsite : InitializerSite m xs) (x : SpecTec.funcidx)
    (hx : SpecTec.instr.«REF.FUNC» x ∈ xs) : RefCyclePrestage.DirectSyntax m x := by
  cases hsite with
  | table t h => exact .table t x h hx
  | global g h => exact .global g x h hx
  | elemInit e xs h hxs => exact .elemInit e xs x h hxs hx
  | elemOffset e a h ha => exact .elemOffset e a x h ha hx
  | dataOffset d a h ha => exact .dataOffset d a x h ha hx

/-- The exact free summary of the unchanged module realizes every reference
needed by each original non-body constant. No additional export or syntax. -/
theorem initializer_final_refs (m : SpecTec.module) (refs : SpecTec.free)
    (freeFinish : Nat)
    (hfree : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.free, SpecTec.Call.«$free_module»
        ({{m with FUNCS := []} with START := none})⟩)
      0 (.success (.of refs)) freeFinish)
    (c : SpecTec.context) (t : SpecTec.valtype) (xs : SpecTec.const)
    (hsite : InitializerSite m xs) (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Const_ok c t xs⟩)
      start (.success (.of ())) finish) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Const_ok {c with REFS := refs} t xs⟩)
      start (.success (.of ())) finish := by
  apply const_ok_replace_refs c refs t xs start finish _ h
  intro x hx
  exact RefCyclePrestage.direct_hasFunc_free m refs freeFinish hfree x
    (initializer_direct m xs hsite x hx)


end properties.wasm_module_ok.ConstructiveRefs
