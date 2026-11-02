import properties.wasm_module_ok.ConstConsumerTrace
import properties.wasm_module_ok.ConstNumericBinopDispatch
import properties.wasm_module_ok.MatchValtypeBasic
import properties.wasm_module_ok.ConstBasicTrace
import properties.wasm_module_ok.ConstDecisionTrace

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstNumericConsumer

theorem match_numeric_pair
    (c : SpecTec.context) (nt : SpecTec.numtype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Match_resulttype c
        [.NumT nt, .NumT nt] [.NumT nt, .NumT nt]⟩)
      n (.success (.of ())) n := by
  apply (MatchResulttypeValidation.match_resulttype_success_iff
    c [.NumT nt, .NumT nt] [.NumT nt, .NumT nt] n n).2
  refine ⟨rfl, ?_⟩
  apply (MatchResulttypeValidation.match_iter_cons_success_iff
    c (.NumT nt) (.NumT nt) [.NumT nt] [.NumT nt] n n).2
  refine ⟨n, ?_, ?_⟩
  · simpa using MatchValtypeBasic.match_valtype_num_total c.TYPES nt nt n
  apply (MatchResulttypeValidation.match_iter_cons_success_iff
    c (.NumT nt) (.NumT nt) [] [] n n).2
  refine ⟨n, ?_, MatchResulttypeValidation.match_iter_nil_total c n⟩
  simpa using MatchValtypeBasic.match_valtype_num_total c.TYPES nt nt n

theorem match_numeric_singleton
    (c : SpecTec.context) (nt : SpecTec.numtype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Match_resulttype c
        [.NumT nt] [.NumT nt]⟩)
      n (.success (.of ())) n := by
  apply (MatchResulttypeValidation.match_resulttype_success_iff
    c [.NumT nt] [.NumT nt] n n).2
  refine ⟨rfl, ?_⟩
  apply (MatchResulttypeValidation.match_iter_cons_success_iff
    c (.NumT nt) (.NumT nt) [] [] n n).2
  refine ⟨n, ?_, MatchResulttypeValidation.match_iter_nil_total c n⟩
  simpa using MatchValtypeBasic.match_valtype_num_total c.TYPES nt nt n

theorem type_num_i32_binop (op : SpecTec.ibinop) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.numtype,
        SpecTec.SpecTecCall.«$type_num»
          SpecTec.ibinop SpecTec.ibinop SpecTec.fbinop SpecTec.fbinop
          (.I32 op)⟩)
      n (.success (.of SpecTec.numtype.I32T)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$type_num_clauses»
        SpecTec.ibinop SpecTec.ibinop SpecTec.fbinop SpecTec.fbinop
        (.I32 op)) ())
    n (.success (.of SpecTec.numtype.I32T)) n
  apply SpecTecExecution.firstSuccess_cons_success
  unfold SpecTec.«$type_num:clause:0»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  · exact SpecTecExecution.Eval.pure _

theorem type_num_i64_binop (op : SpecTec.ibinop) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.numtype,
        SpecTec.SpecTecCall.«$type_num»
          SpecTec.ibinop SpecTec.ibinop SpecTec.fbinop SpecTec.fbinop
          (.I64 op)⟩)
      n (.success (.of SpecTec.numtype.I64T)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$type_num_clauses»
        SpecTec.ibinop SpecTec.ibinop SpecTec.fbinop SpecTec.fbinop
        (.I64 op)) ())
    n (.success (.of SpecTec.numtype.I64T)) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  ·
    unfold SpecTec.«$type_num:clause:0»
    apply SpecTecExecution.Eval.bind_unmatch
    exact SpecTecExecution.Eval.guard_false
      (by simp [SpecTec.«exec:match:op:I32»])
  apply SpecTecExecution.firstSuccess_cons_success
  unfold SpecTec.«$type_num:clause:1»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  · exact SpecTecExecution.Eval.pure _

theorem allowed_arithmetic_type
    (op : SpecTec.binop_) (n : Nat)
    (h : SpecTec.instr.BINOP op ∈
      ConstArithmeticValidation.arithmeticOps) :
    ∃ nt : SpecTec.numtype,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.numtype,
          SpecTec.SpecTecCall.«$type_num»
            SpecTec.ibinop SpecTec.ibinop
            SpecTec.fbinop SpecTec.fbinop op⟩)
        n (.success (.of nt)) n := by
  simp [ConstArithmeticValidation.arithmeticOps] at h
  rcases h with h | h | h | h | h | h
  · subst op
    exact ⟨.I32T, type_num_i32_binop .IAdd n⟩
  · subst op
    exact ⟨.I32T, type_num_i32_binop .ISub n⟩
  · subst op
    exact ⟨.I32T, type_num_i32_binop .IMul n⟩
  · subst op
    exact ⟨.I64T, type_num_i64_binop .IAdd n⟩
  · subst op
    exact ⟨.I64T, type_num_i64_binop .ISub n⟩
  · subst op
    exact ⟨.I64T, type_num_i64_binop .IMul n⟩

theorem append_numeric_binop
    {origin current : SpecTec.context}
    {initial : SpecTec.inferresulttype}
    {xs : List SpecTec.instr}
    {start n : Nat}
    (stack : List SpecTec.valtype) (nt : SpecTec.numtype)
    (op : SpecTec.binop_)
    (htrace : ConstConstructiveTrace.Trace origin initial xs current
      (.NoEllipses, stack ++ [.NumT nt, .NumT nt]) start n)
    (htype : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.numtype,
        SpecTec.SpecTecCall.«$type_num»
          SpecTec.ibinop SpecTec.ibinop SpecTec.fbinop SpecTec.fbinop op⟩)
      n (.success (.of nt)) n) :
    ConstConstructiveTrace.Trace origin initial (xs ++ [.BINOP op]) current
      (.NoEllipses, stack ++ [.NumT nt]) start n := by
  have hinstr :=
    (ConstNumericBinopDispatch.numeric_binop_dispatch_iff current
      (.NoEllipses, stack ++ [.NumT nt, .NumT nt]) op
      (⟨{ INS := (.NoEllipses, [.NumT nt, .NumT nt]),
           OUTS := (.NoEllipses, [.NumT nt]) },
         ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype)
      n n).2 ⟨nt, htype, rfl⟩
  have hmatch : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Match_resulttype current
        ((stack ++ ([.NumT nt, .NumT nt] : List SpecTec.valtype)).drop
          ((stack ++ ([.NumT nt, .NumT nt] : List SpecTec.valtype)).length - 2))
        [.NumT nt, .NumT nt]⟩)
      n (.success (.of ())) n := by
    simpa using match_numeric_pair current nt n
  have hconsumer := ConstConsumerTrace.trace_snoc_of_match
    (stack ++ [.NumT nt, .NumT nt])
    [.NumT nt, .NumT nt] (.NumT nt) (.BINOP op)
    htrace hinstr (by simp) hmatch
  simpa only [List.length_append, List.length_cons,
    List.length_nil, Nat.zero_add, Nat.add_sub_cancel_right,
    List.take_append, List.take_of_length_le,
    Nat.sub_self, List.take_zero, List.take_length,
    List.nil_append,
    List.append_assoc] using hconsumer

theorem i32_add_const_expression
    (c : SpecTec.context) (n : Nat) :
    ∃ xs : List SpecTec.instr,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit, SpecTec.SpecTecCall.Const_ok c
          (.NumT .I32T) xs⟩)
        n (.success (.of ())) n := by
  have hbase : SpecTec.valtype.NumT .I32T ∈
      ConstBasicSeed.basicBase c := by
    exact (ConstBasicSeed.basic_base_mem_iff c _).2
      (by simp [ConstBasicSeed.basicSeed,
        ConstLiteralProduction.literalSeed,
        ConstNumericProduction.numericSeed])
  obtain ⟨xs, hsyntax, htrace⟩ :=
    ConstBasicTrace.basic_list_trace c c
      (ConstStaticAgreement.refl c)
      [.NumT .I32T, .NumT .I32T]
      (by
        intro u hu
        have heq : u = SpecTec.valtype.NumT .I32T := by
          simpa using hu
        subst u
        exact hbase)
      [] n
  have hbinop := append_numeric_binop [] .I32T (.I32 .IAdd)
    (by simpa using htrace)
    (type_num_i32_binop .IAdd n)
  have hpop : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.SpecTecCall.«$pop» c
          (.NoEllipses, [.NumT .I32T])
          (.NoEllipses, [.NumT .I32T])⟩)
      n (.success (.of (SpecTec.ellipses.NoEllipses,
        ([] : List SpecTec.valtype)))) n := by
    simpa using
      (PopGeneralValidation.pop_noellipses_of_match c
        [.NumT .I32T] [.NumT .I32T] n n
        (by simp) (by simpa using match_numeric_singleton c .I32T n))
  refine ⟨xs ++ [.BINOP (.I32 .IAdd)],
    (ConstDecisionTrace.const_ok_decision_trace_iff
      c (.NumT .I32T) (xs ++ [.BINOP (.I32 .IAdd)]) n n).2 ?_⟩
  refine ⟨?_, (.NoEllipses, [.NumT .I32T]),
    ([] : List SpecTec.idx), .NoEllipses, n, ?_, hpop⟩
  · intro i hi
    simp only [List.mem_append, List.mem_singleton] at hi
    rcases hi with hi | rfl
    · exact hsyntax i hi
    · simp [ConstSyntaxDecision.syntaxAllowed,
        ConstArithmeticValidation.arithmeticOps]
  · exact ConstConstructiveTrace.trace_to_instrs
      (by simpa using hbinop)

theorem numeric_binop_const_expression
    (c : SpecTec.context) (n : Nat)
    (nt : SpecTec.numtype) (op : SpecTec.binop_)
    (hallowed : SpecTec.instr.BINOP op ∈
      ConstArithmeticValidation.arithmeticOps)
    (htype : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.numtype,
        SpecTec.SpecTecCall.«$type_num»
          SpecTec.ibinop SpecTec.ibinop
          SpecTec.fbinop SpecTec.fbinop op⟩)
      n (.success (.of nt)) n) :
    ∃ xs : List SpecTec.instr,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit, SpecTec.SpecTecCall.Const_ok c
          (.NumT nt) xs⟩)
        n (.success (.of ())) n := by
  have hbase : SpecTec.valtype.NumT nt ∈
      ConstBasicSeed.basicBase c := by
    exact (ConstBasicSeed.basic_base_mem_iff c _).2
      (by simp [ConstBasicSeed.basicSeed,
        ConstLiteralProduction.literalSeed,
        ConstNumericProduction.numericSeed])
  obtain ⟨xs, hsyntax, htrace⟩ :=
    ConstBasicTrace.basic_list_trace c c
      (ConstStaticAgreement.refl c)
      [.NumT nt, .NumT nt]
      (by
        intro u hu
        have heq : u = SpecTec.valtype.NumT nt := by
          simpa using hu
        subst u
        exact hbase)
      [] n
  have hbinop := append_numeric_binop [] nt op
    (by simpa using htrace) htype
  have hpop : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.SpecTecCall.«$pop» c
          (.NoEllipses, [.NumT nt])
          (.NoEllipses, [.NumT nt])⟩)
      n (.success (.of (SpecTec.ellipses.NoEllipses,
        ([] : List SpecTec.valtype)))) n := by
    simpa using
      (PopGeneralValidation.pop_noellipses_of_match c
        [.NumT nt] [.NumT nt] n n
        (by simp) (by simpa using match_numeric_singleton c nt n))
  refine ⟨xs ++ [.BINOP op],
    (ConstDecisionTrace.const_ok_decision_trace_iff
      c (.NumT nt) (xs ++ [.BINOP op]) n n).2 ?_⟩
  refine ⟨?_, (.NoEllipses, [.NumT nt]),
    ([] : List SpecTec.idx), .NoEllipses, n, ?_, hpop⟩
  · intro i hi
    simp only [List.mem_append, List.mem_singleton] at hi
    rcases hi with hi | rfl
    · exact hsyntax i hi
    · simp [ConstSyntaxDecision.syntaxAllowed, hallowed]
  · exact ConstConstructiveTrace.trace_to_instrs
      (by simpa using hbinop)

theorem allowed_arithmetic_const_expression
    (c : SpecTec.context) (n : Nat) (op : SpecTec.binop_)
    (hallowed : SpecTec.instr.BINOP op ∈
      ConstArithmeticValidation.arithmeticOps) :
    ∃ (nt : SpecTec.numtype) (xs : List SpecTec.instr),
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit, SpecTec.SpecTecCall.Const_ok c
          (.NumT nt) xs⟩)
        n (.success (.of ())) n := by
  obtain ⟨nt, htype⟩ := allowed_arithmetic_type op n hallowed
  obtain ⟨xs, hconst⟩ :=
    numeric_binop_const_expression c n nt op hallowed htype
  exact ⟨nt, xs, hconst⟩

end properties.wasm_module_ok.ConstNumericConsumer
