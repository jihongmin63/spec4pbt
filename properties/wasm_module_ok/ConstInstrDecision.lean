import properties.wasm_module_ok.ConstLiteralDispatch
import properties.wasm_module_ok.ConstVectorDispatch
import properties.wasm_module_ok.ConstRefNullDispatch
import properties.wasm_module_ok.ConstRefFuncEffect
import properties.wasm_module_ok.ConstGlobalGetDispatch
import properties.wasm_module_ok.ConstNumericConsumer
import properties.wasm_module_ok.ConstNumericBinopDispatch
import properties.wasm_module_ok.ConstI31Dispatch
import properties.wasm_module_ok.ConstExternConvertDispatch
import properties.wasm_module_ok.ExternopTypeDecision
import properties.wasm_module_ok.PeekRefDecision
import properties.wasm_module_ok.ConstStructImplicitDispatch
import properties.wasm_module_ok.StructTypeDecision
import properties.wasm_module_ok.StructImplicitFieldsDecision
import properties.wasm_module_ok.ConstStructExplicitDispatch
import properties.wasm_module_ok.StructExplicitFieldsDecision
import properties.wasm_module_ok.ConstArrayImplicitDispatch
import properties.wasm_module_ok.ArrayTypeDecision
import properties.wasm_module_ok.UnpackedFieldDecision
import properties.wasm_module_ok.DefaultableValidation
import properties.wasm_module_ok.ConstArrayExplicitDispatch
import properties.wasm_module_ok.ConstArrayFixedDispatch
import properties.wasm_module_ok.MakeValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstInstrDecision

def numericLiteralResult (v : SpecTec.num_) :
    Option SpecTec.inferinstrtype :=
  some
    (⟨{ INS := (.NoEllipses, []),
         OUTS := (.NoEllipses,
           [.NumT (ConstLiteralEffect.numericType v)]) },
      ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype)

theorem numeric_literal_result_iff
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (v : SpecTec.num_) (iit : SpecTec.inferinstrtype)
    (start finish : Nat) :
    numericLiteralResult v = some iit ∧ finish = start ↔
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.inferinstrtype,
          SpecTec.SpecTecCall.Instr_ok c irt (.CONST v)⟩)
        start (.success (.of iit)) finish := by
  constructor
  · rintro ⟨hresult, rfl⟩
    simp only [numericLiteralResult, Option.some.injEq] at hresult
    subst iit
    exact ConstLiteralDispatch.const_dispatch_total c irt v finish
  · intro hcall
    obtain ⟨hresult, hfinish⟩ :=
      ConstLiteralDispatch.const_literal_effect
        c irt v iit start finish hcall
    exact ⟨by simp [numericLiteralResult, hresult], hfinish⟩

def vectorLiteralResult : SpecTec.inferinstrtype :=
  ⟨{ INS := (.NoEllipses, []),
       OUTS := (.NoEllipses, [.VecT .V128T]) },
    ([] : List SpecTec.localidx)⟩

theorem vector_literal_result_iff
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (v : SpecTec.vec_) (iit : SpecTec.inferinstrtype)
    (start finish : Nat) :
    some vectorLiteralResult = some iit ∧ finish = start ↔
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.inferinstrtype,
          SpecTec.SpecTecCall.Instr_ok c irt (.«VEC.CONST» v)⟩)
        start (.success (.of iit)) finish := by
  constructor
  · rintro ⟨hresult, rfl⟩
    simp only [Option.some.injEq] at hresult
    subst iit
    exact ConstVectorDispatch.vec_dispatch_total c irt v finish
  · intro hcall
    obtain ⟨hresult, hfinish⟩ :=
      ConstVectorDispatch.vec_literal_effect
        c irt v iit start finish hcall
    exact ⟨by simp [vectorLiteralResult, hresult], hfinish⟩

def refNullResult (c : SpecTec.context) (ht : SpecTec.heaptype) :
    Option SpecTec.inferinstrtype :=
  if HeaptypeValidation.heaptypeValid c ht then
    some
      (⟨{ INS := (.NoEllipses, []),
           OUTS := (.NoEllipses, [.RefT (.«% %» .Null ht)]) },
        ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype)
  else none

theorem ref_null_result_iff
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (ht : SpecTec.heaptype) (iit : SpecTec.inferinstrtype)
    (start finish : Nat) :
    refNullResult c ht = some iit ∧ finish = start ↔
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.inferinstrtype,
          SpecTec.SpecTecCall.Instr_ok c irt (.«REF.NULL» ht)⟩)
        start (.success (.of iit)) finish := by
  rw [ConstRefNullDispatch.ref_null_dispatch_iff]
  constructor
  · rintro ⟨hresult, hfinish⟩
    by_cases hvalid : HeaptypeValidation.heaptypeValid c ht = true
    · simp only [refNullResult, if_pos hvalid, Option.some.injEq] at hresult
      exact ⟨hvalid, hresult.symm, hfinish⟩
    · simp [refNullResult, hvalid] at hresult
  · rintro ⟨hvalid, hiit, hfinish⟩
    subst iit
    exact ⟨by simp [refNullResult, hvalid], hfinish⟩

def refFuncAllowed (c : SpecTec.context) (x : SpecTec.funcidx) : Bool :=
  match c.REFS.FUNCS with
  | .«`{ % `}» xs => decide (x ∈ xs)

theorem ref_func_allowed_iff
    (c : SpecTec.context) (x : SpecTec.funcidx) :
    refFuncAllowed c x = true ↔
      FreeUnionValidation.HasFunc c.REFS x := by
  cases h : c.REFS.FUNCS with
  | «`{ % `}» xs =>
      simp [refFuncAllowed, FreeUnionValidation.HasFunc, h]

def refFuncResult (c : SpecTec.context) (x : SpecTec.funcidx) :
    Option SpecTec.inferinstrtype :=
  match c.FUNCS[x]? with
  | none => none
  | some dt =>
      if refFuncAllowed c x then
        some
          (⟨{ INS := (.NoEllipses, []),
               OUTS := (.NoEllipses,
                 [.RefT (.«% %» .NoNull (.DefHT dt))]) },
            ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype)
      else none

theorem ref_func_result_iff
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.funcidx) (iit : SpecTec.inferinstrtype)
    (start finish : Nat) :
    refFuncResult c x = some iit ∧ finish = start ↔
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.inferinstrtype,
          SpecTec.SpecTecCall.Instr_ok c irt (.«REF.FUNC» x)⟩)
        start (.success (.of iit)) finish := by
  rw [ConstRefFuncEffect.ref_func_instruction_iff]
  constructor
  · rintro ⟨hresult, hfinish⟩
    cases hget : c.FUNCS[x]? with
    | none => simp [refFuncResult, hget] at hresult
    | some dt =>
        by_cases hallowed : refFuncAllowed c x = true
        · simp only [refFuncResult, hget, if_pos hallowed,
            Option.some.injEq] at hresult
          exact ⟨dt, rfl, (ref_func_allowed_iff c x).1 hallowed,
            hresult.symm, hfinish⟩
        · simp [refFuncResult, hget, hallowed] at hresult
  · rintro ⟨dt, hget, href, hiit, hfinish⟩
    have hallowed := (ref_func_allowed_iff c x).2 href
    subst iit
    exact ⟨by simp [refFuncResult, hget, hallowed], hfinish⟩

def globalGetResult (c : SpecTec.context) (x : SpecTec.globalidx) :
    Option SpecTec.inferinstrtype :=
  match c.GLOBALS[x]? with
  | none => none
  | some (.GlobalT _ t) =>
      some
        (⟨{ INS := (.NoEllipses, []),
             OUTS := (.NoEllipses, [t]) },
          ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype)

theorem global_get_result_iff
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.globalidx) (iit : SpecTec.inferinstrtype)
    (start finish : Nat) :
    globalGetResult c x = some iit ∧ finish = start ↔
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.inferinstrtype,
          SpecTec.SpecTecCall.Instr_ok c irt (.«GLOBAL.GET» x)⟩)
        start (.success (.of iit)) finish := by
  rw [ConstGlobalGetDispatch.global_get_dispatch_iff]
  constructor
  · rintro ⟨hresult, hfinish⟩
    cases hget : c.GLOBALS[x]? with
    | none => simp [globalGetResult, hget] at hresult
    | some gt =>
        cases gt with
        | GlobalT m t =>
            simp only [globalGetResult, hget, Option.some.injEq] at hresult
            exact ⟨m, t, rfl, hresult.symm, hfinish⟩
  · rintro ⟨m, t, hget, hiit, hfinish⟩
    subst iit
    exact ⟨by simp [globalGetResult, hget], hfinish⟩

def arithmeticType : SpecTec.binop_ → SpecTec.numtype
  | .I32 _ => .I32T
  | .I64 _ => .I64T
  | .F32 _ => .F32T
  | .F64 _ => .F64T

theorem allowed_arithmetic_type_call
    (op : SpecTec.binop_) (n : Nat)
    (hallowed : SpecTec.instr.BINOP op ∈
      ConstArithmeticValidation.arithmeticOps) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.numtype,
        SpecTec.SpecTecCall.«$type_num»
          SpecTec.ibinop SpecTec.ibinop
          SpecTec.fbinop SpecTec.fbinop op⟩)
      n (.success (.of (arithmeticType op))) n := by
  simp [ConstArithmeticValidation.arithmeticOps] at hallowed
  rcases hallowed with h | h | h | h | h | h
  · subst op
    simpa [arithmeticType] using
      (ConstNumericConsumer.type_num_i32_binop .IAdd n)
  · subst op
    simpa [arithmeticType] using
      (ConstNumericConsumer.type_num_i32_binop .ISub n)
  · subst op
    simpa [arithmeticType] using
      (ConstNumericConsumer.type_num_i32_binop .IMul n)
  · subst op
    simpa [arithmeticType] using
      (ConstNumericConsumer.type_num_i64_binop .IAdd n)
  · subst op
    simpa [arithmeticType] using
      (ConstNumericConsumer.type_num_i64_binop .ISub n)
  · subst op
    simpa [arithmeticType] using
      (ConstNumericConsumer.type_num_i64_binop .IMul n)

def arithmeticResult (op : SpecTec.binop_) :
    Option SpecTec.inferinstrtype :=
  if SpecTec.instr.BINOP op ∈ ConstArithmeticValidation.arithmeticOps then
    some
      (⟨{ INS := (.NoEllipses,
              [.NumT (arithmeticType op), .NumT (arithmeticType op)]),
           OUTS := (.NoEllipses, [.NumT (arithmeticType op)]) },
        ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype)
  else none

theorem arithmetic_result_iff
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (op : SpecTec.binop_) (iit : SpecTec.inferinstrtype)
    (start finish : Nat) :
    arithmeticResult op = some iit ∧ finish = start ↔
      ConstSyntaxDecision.syntaxAllowed c (.BINOP op) = true ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.inferinstrtype,
          SpecTec.SpecTecCall.Instr_ok c irt (.BINOP op)⟩)
        start (.success (.of iit)) finish := by
  rw [ConstNumericBinopDispatch.numeric_binop_constant_instruction_iff]
  constructor
  · rintro ⟨hresult, hfinish⟩
    by_cases hallowed : SpecTec.instr.BINOP op ∈
        ConstArithmeticValidation.arithmeticOps
    · simp only [arithmeticResult, if_pos hallowed,
        Option.some.injEq] at hresult
      subst finish
      exact ⟨hallowed, arithmeticType op,
        allowed_arithmetic_type_call op start hallowed,
        hresult.symm⟩
    · simp [arithmeticResult, hallowed] at hresult
  · rintro ⟨hallowed, nt, htype, hiit⟩
    have hdet : SpecTecExecution.PrimitiveDeterministic
        SpecTec.specTecProgram := by
      intro request a b hp
      cases hp
    obtain ⟨hvalue, hfinish⟩ :=
      SpecTecExecution.eval_deterministic hdet htype
        (allowed_arithmetic_type_call op start hallowed)
    cases hvalue
    subst iit
    exact ⟨by simp [arithmeticResult, hallowed], hfinish⟩

def i31Result : SpecTec.inferinstrtype :=
  ⟨{ INS := (.NoEllipses, [.NumT .I32T]),
       OUTS := (.NoEllipses,
         [.RefT (.«% %» .NoNull .I31HT)]) },
    ([] : List SpecTec.localidx)⟩

theorem i31_result_iff
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (iit : SpecTec.inferinstrtype) (start finish : Nat) :
    some i31Result = some iit ∧ finish = start ↔
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.inferinstrtype,
          SpecTec.SpecTecCall.Instr_ok c irt .«REF.I31»⟩)
        start (.success (.of iit)) finish := by
  constructor
  · rintro ⟨hresult, rfl⟩
    simp only [Option.some.injEq] at hresult
    subst iit
    exact ConstI31Dispatch.i31_dispatch_total c irt finish
  · intro hcall
    obtain ⟨hresult, hfinish⟩ :=
      ConstI31Dispatch.i31_instruction_effect
        c irt iit start finish hcall
    exact ⟨by simp [i31Result, hresult], hfinish⟩

def externConvertResult (op : SpecTec.externop_)
    (irt : SpecTec.inferresulttype) : Option SpecTec.inferinstrtype :=
  let (ht1, ht2) := ExternopTypeDecision.typeExternopResult op
  match PeekRefDecision.peekRefResult (PeekDecision.peekResult 0 irt) with
  | none => none
  | some (.«% %» nu _) =>
      some
        (⟨{ INS := (.NoEllipses, [.RefT (.«% %» nu ht1)]),
             OUTS := (.NoEllipses, [.RefT (.«% %» nu ht2)]) },
          ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype)

theorem extern_convert_result_iff
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (op : SpecTec.externop_) (iit : SpecTec.inferinstrtype)
    (start finish : Nat) :
    externConvertResult op irt = some iit ∧ finish = start ↔
      ConstSyntaxDecision.syntaxAllowed c (.«EXTERN.CONVERT» op) = true ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.inferinstrtype,
          SpecTec.SpecTecCall.Instr_ok c irt (.«EXTERN.CONVERT» op)⟩)
        start (.success (.of iit)) finish := by
  rw [ConstExternConvertDispatch.extern_convert_constant_instruction_iff]
  constructor
  · rintro ⟨hresult, rfl⟩
    cases hpair : ExternopTypeDecision.typeExternopResult op with
    | mk ht1 ht2 =>
      cases hpeek : PeekRefDecision.peekRefResult
          (PeekDecision.peekResult 0 irt) with
      | none => simp [externConvertResult, hpeek] at hresult
      | some rt =>
        cases rt with
        | «% %» nu ht =>
          simp only [externConvertResult, hpair, hpeek,
            Option.some.injEq] at hresult
          subst iit
          refine ⟨ht1, ht2, nu, ht, finish, ?_, ?_, rfl⟩
          · simpa [hpair] using
              (ExternopTypeDecision.type_externop_total op finish)
          · exact PeekRefDecision.peek_ref_total_of_some 0 irt
              (.«% %» nu ht) finish hpeek
  · rintro ⟨ht1, ht2, nu, ht, middle, htype, hpeek, hiit⟩
    obtain ⟨hpair, hmiddle⟩ :=
      (ExternopTypeDecision.type_externop_success_iff_result
        op (ht1, ht2) start middle).1 htype
    obtain ⟨hpeekResult, hfinish⟩ :=
      (PeekRefDecision.peek_ref_success_iff_result
        0 irt (.«% %» nu ht) middle finish).1 hpeek
    have hcounter : finish = start := by omega
    constructor
    · cases hactual : ExternopTypeDecision.typeExternopResult op with
      | mk actual1 actual2 =>
        have hparts : ht1 = actual1 ∧ ht2 = actual2 := by
          simpa [hactual] using hpair
        rcases hparts with ⟨rfl, rfl⟩
        subst iit
        simp [externConvertResult, hactual, hpeekResult]
    · exact hcounter

def structImplicitResult (c : SpecTec.context) (x : SpecTec.typeidx) :
    Option SpecTec.inferinstrtype :=
  match StructTypeDecision.structTypeResult c x, c.TYPES[x]? with
  | some (.StructT ys), some dt =>
      if StructImplicitFieldsDecision.structFieldsDefaultable ys then
        some
          (⟨{ INS := (.NoEllipses, []),
               OUTS := (.NoEllipses,
                 [.RefT (.«% %» .NoNull (.DefHT dt))]) },
            ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype)
      else none
  | _, _ => none

theorem struct_implicit_result_iff
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.typeidx) (iit : SpecTec.inferinstrtype)
    (start finish : Nat) :
    structImplicitResult c x = some iit ∧ finish = start ↔
      ConstSyntaxDecision.syntaxAllowed c (.«STRUCT.NEW» x .Implicit) = true ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.inferinstrtype,
          SpecTec.SpecTecCall.Instr_ok c irt (.«STRUCT.NEW» x .Implicit)⟩)
        start (.success (.of iit)) finish := by
  rw [ConstStructImplicitDispatch.struct_new_implicit_constant_instruction_iff]
  constructor
  · rintro ⟨hresult, rfl⟩
    cases hstruct : StructTypeDecision.structTypeResult c x with
    | none => simp [structImplicitResult, hstruct] at hresult
    | some strct =>
      cases strct with
      | StructT ys =>
        cases hget : c.TYPES[x]? with
        | none => simp [structImplicitResult, hstruct, hget] at hresult
        | some dt =>
          by_cases hdefault :
              StructImplicitFieldsDecision.structFieldsDefaultable ys = true
          · simp only [structImplicitResult, hstruct, hget,
              if_pos hdefault, Option.some.injEq] at hresult
            subst iit
            refine ⟨ys, dt, finish, ?_, ?_, rfl, rfl⟩
            · exact (StructTypeDecision.struct_type_success_iff_result
                c x (.StructT ys) finish finish).2 ⟨hstruct, rfl⟩
            · exact (StructImplicitFieldsDecision.fields_success_iff_defaultable
                ys finish finish).2 ⟨hdefault, rfl⟩
          · simp [structImplicitResult, hstruct, hget, hdefault] at hresult
  · rintro ⟨ys, dt, middle, hstructCall, hfieldsCall, hget, hiit⟩
    obtain ⟨hstruct, hmiddle⟩ :=
      (StructTypeDecision.struct_type_success_iff_result
        c x (.StructT ys) start middle).1 hstructCall
    obtain ⟨hdefault, hfinish⟩ :=
      (StructImplicitFieldsDecision.fields_success_iff_defaultable
        ys middle finish).1 hfieldsCall
    subst iit
    exact ⟨by simp [structImplicitResult, hstruct, hget, hdefault],
      hfinish.trans hmiddle⟩

def structExplicitResult (c : SpecTec.context) (x : SpecTec.typeidx) :
    Option SpecTec.inferinstrtype :=
  match StructTypeDecision.structTypeResult c x, c.TYPES[x]? with
  | some (.StructT ys), some dt =>
      some
        (⟨{ INS := (.NoEllipses,
                 StructExplicitFieldsDecision.structFieldInputs ys),
             OUTS := (.NoEllipses,
               [.RefT (.«% %» .NoNull (.DefHT dt))]) },
          ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype)
  | _, _ => none

theorem struct_explicit_result_iff
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.typeidx) (iit : SpecTec.inferinstrtype)
    (start finish : Nat) :
    structExplicitResult c x = some iit ∧ finish = start ↔
      ConstSyntaxDecision.syntaxAllowed c (.«STRUCT.NEW» x .Explicit) = true ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.inferinstrtype,
          SpecTec.SpecTecCall.Instr_ok c irt (.«STRUCT.NEW» x .Explicit)⟩)
        start (.success (.of iit)) finish := by
  rw [ConstStructExplicitDispatch.struct_new_explicit_constant_instruction_iff]
  constructor
  · rintro ⟨hresult, rfl⟩
    cases hstruct : StructTypeDecision.structTypeResult c x with
    | none => simp [structExplicitResult, hstruct] at hresult
    | some strct =>
      cases strct with
      | StructT ys =>
        cases hget : c.TYPES[x]? with
        | none => simp [structExplicitResult, hstruct, hget] at hresult
        | some dt =>
          simp only [structExplicitResult, hstruct, hget,
            Option.some.injEq] at hresult
          subst iit
          refine ⟨ys, StructExplicitFieldsDecision.structFieldInputs ys,
            dt, finish, ?_, ?_, rfl, rfl⟩
          · exact (StructTypeDecision.struct_type_success_iff_result
              c x (.StructT ys) finish finish).2 ⟨hstruct, rfl⟩
          · exact (StructExplicitFieldsDecision.fields_success_iff_inputs
              ys (StructExplicitFieldsDecision.structFieldInputs ys)
              finish finish).2 ⟨rfl, rfl⟩
  · rintro ⟨ys, ts, dt, middle, hstructCall, hfieldsCall, hget, hiit⟩
    obtain ⟨hstruct, hmiddle⟩ :=
      (StructTypeDecision.struct_type_success_iff_result
        c x (.StructT ys) start middle).1 hstructCall
    obtain ⟨hinputs, hfinish⟩ :=
      (StructExplicitFieldsDecision.fields_success_iff_inputs
        ys ts middle finish).1 hfieldsCall
    subst ts
    subst iit
    exact ⟨by simp [structExplicitResult, hstruct, hget],
      hfinish.trans hmiddle⟩

def arrayImplicitResult (c : SpecTec.context) (x : SpecTec.typeidx) :
    Option SpecTec.inferinstrtype :=
  match ArrayTypeDecision.arrayTypeResult c x, c.TYPES[x]? with
  | some (.ArrayT yt), some dt =>
      if DefaultableValidation.defaultable
          (UnpackedFieldDecision.unpackedFieldResult yt) then
        some
          (⟨{ INS := (.NoEllipses, [.NumT .I32T]),
               OUTS := (.NoEllipses,
                 [.RefT (.«% %» .NoNull (.DefHT dt))]) },
            ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype)
      else none
  | _, _ => none

theorem array_implicit_result_iff
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.typeidx) (iit : SpecTec.inferinstrtype)
    (start finish : Nat) :
    arrayImplicitResult c x = some iit ∧ finish = start ↔
      ConstSyntaxDecision.syntaxAllowed c (.«ARRAY.NEW» x .Implicit) = true ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.inferinstrtype,
          SpecTec.SpecTecCall.Instr_ok c irt (.«ARRAY.NEW» x .Implicit)⟩)
        start (.success (.of iit)) finish := by
  rw [ConstArrayImplicitDispatch.array_new_implicit_constant_instruction_iff]
  constructor
  · rintro ⟨hresult, rfl⟩
    cases harray : ArrayTypeDecision.arrayTypeResult c x with
    | none => simp [arrayImplicitResult, harray] at hresult
    | some arr =>
      cases arr with
      | ArrayT yt =>
        cases hget : c.TYPES[x]? with
        | none => simp [arrayImplicitResult, harray, hget] at hresult
        | some dt =>
          by_cases hdefault : DefaultableValidation.defaultable
              (UnpackedFieldDecision.unpackedFieldResult yt) = true
          · simp only [arrayImplicitResult, harray, hget,
              if_pos hdefault, Option.some.injEq] at hresult
            subst iit
            refine ⟨yt, UnpackedFieldDecision.unpackedFieldResult yt,
              dt, finish, finish, ?_, ?_, ?_, rfl, rfl⟩
            · exact (ArrayTypeDecision.array_type_success_iff_result
                c x (.ArrayT yt) finish finish).2 ⟨harray, rfl⟩
            · exact (UnpackedFieldDecision.unpacked_field_success_iff_result
                yt (UnpackedFieldDecision.unpackedFieldResult yt)
                finish finish).2 ⟨rfl, rfl⟩
            · exact (DefaultableValidation.defaultable_success_iff
                (UnpackedFieldDecision.unpackedFieldResult yt)
                true finish finish).2 ⟨hdefault.symm, rfl⟩
          · simp [arrayImplicitResult, harray, hget, hdefault] at hresult
  · rintro ⟨yt, t, dt, middle, after, harrayCall,
      hunpackCall, hdefaultCall, hget, hiit⟩
    obtain ⟨harray, hmiddle⟩ :=
      (ArrayTypeDecision.array_type_success_iff_result
        c x (.ArrayT yt) start middle).1 harrayCall
    obtain ⟨ht, hafter⟩ :=
      (UnpackedFieldDecision.unpacked_field_success_iff_result
        yt t middle after).1 hunpackCall
    obtain ⟨hb, hfinish⟩ :=
      (DefaultableValidation.defaultable_success_iff
        t true after finish).1 hdefaultCall
    subst t
    subst iit
    exact ⟨by simp [arrayImplicitResult, harray, hget, hb.symm],
      hfinish.trans (hafter.trans hmiddle)⟩

def arrayExplicitResult (c : SpecTec.context) (x : SpecTec.typeidx) :
    Option SpecTec.inferinstrtype :=
  match ArrayTypeDecision.arrayTypeResult c x, c.TYPES[x]? with
  | some (.ArrayT yt), some dt =>
      some
        (⟨{ INS := (.NoEllipses,
                 [UnpackedFieldDecision.unpackedFieldResult yt,
                  .NumT .I32T]),
             OUTS := (.NoEllipses,
               [.RefT (.«% %» .NoNull (.DefHT dt))]) },
          ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype)
  | _, _ => none

theorem array_explicit_result_iff
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.typeidx) (iit : SpecTec.inferinstrtype)
    (start finish : Nat) :
    arrayExplicitResult c x = some iit ∧ finish = start ↔
      ConstSyntaxDecision.syntaxAllowed c (.«ARRAY.NEW» x .Explicit) = true ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.inferinstrtype,
          SpecTec.SpecTecCall.Instr_ok c irt (.«ARRAY.NEW» x .Explicit)⟩)
        start (.success (.of iit)) finish := by
  rw [ConstArrayExplicitDispatch.array_new_explicit_constant_instruction_iff]
  constructor
  · rintro ⟨hresult, rfl⟩
    cases harray : ArrayTypeDecision.arrayTypeResult c x with
    | none => simp [arrayExplicitResult, harray] at hresult
    | some arr =>
      cases arr with
      | ArrayT yt =>
        cases hget : c.TYPES[x]? with
        | none => simp [arrayExplicitResult, harray, hget] at hresult
        | some dt =>
          simp only [arrayExplicitResult, harray, hget,
            Option.some.injEq] at hresult
          subst iit
          refine ⟨yt, UnpackedFieldDecision.unpackedFieldResult yt,
            dt, finish, ?_, ?_, rfl, rfl⟩
          · exact (ArrayTypeDecision.array_type_success_iff_result
              c x (.ArrayT yt) finish finish).2 ⟨harray, rfl⟩
          · exact (UnpackedFieldDecision.unpacked_field_success_iff_result
              yt (UnpackedFieldDecision.unpackedFieldResult yt)
              finish finish).2 ⟨rfl, rfl⟩
  · rintro ⟨yt, t, dt, middle, harrayCall, hunpackCall, hget, hiit⟩
    obtain ⟨harray, hmiddle⟩ :=
      (ArrayTypeDecision.array_type_success_iff_result
        c x (.ArrayT yt) start middle).1 harrayCall
    obtain ⟨ht, hfinish⟩ :=
      (UnpackedFieldDecision.unpacked_field_success_iff_result
        yt t middle finish).1 hunpackCall
    subst t
    subst iit
    exact ⟨by simp [arrayExplicitResult, harray, hget],
      hfinish.trans hmiddle⟩

def arrayFixedResult (c : SpecTec.context) (x : SpecTec.typeidx)
    (count : SpecTec.n) : Option SpecTec.inferinstrtype :=
  match ArrayTypeDecision.arrayTypeResult c x, c.TYPES[x]? with
  | some (.ArrayT yt), some dt =>
      some
        (⟨{ INS := (.NoEllipses,
                 MakeValidation.makeResult
                   (UnpackedFieldDecision.unpackedFieldResult yt) count),
             OUTS := (.NoEllipses,
               [.RefT (.«% %» .NoNull (.DefHT dt))]) },
          ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype)
  | _, _ => none

theorem array_fixed_result_iff
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.typeidx) (count : SpecTec.n)
    (iit : SpecTec.inferinstrtype) (start finish : Nat) :
    arrayFixedResult c x count = some iit ∧ finish = start ↔
      ConstSyntaxDecision.syntaxAllowed c (.«ARRAY.NEW_FIXED» x count) = true ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.inferinstrtype,
          SpecTec.SpecTecCall.Instr_ok c irt
            (.«ARRAY.NEW_FIXED» x count)⟩)
        start (.success (.of iit)) finish := by
  rw [ConstArrayFixedDispatch.array_new_fixed_constant_instruction_iff]
  constructor
  · rintro ⟨hresult, rfl⟩
    cases harray : ArrayTypeDecision.arrayTypeResult c x with
    | none => simp [arrayFixedResult, harray] at hresult
    | some arr =>
      cases arr with
      | ArrayT yt =>
        cases hget : c.TYPES[x]? with
        | none => simp [arrayFixedResult, harray, hget] at hresult
        | some dt =>
          simp only [arrayFixedResult, harray, hget,
            Option.some.injEq] at hresult
          subst iit
          refine ⟨yt, UnpackedFieldDecision.unpackedFieldResult yt,
            dt, finish, ?_, ?_, rfl, rfl⟩
          · exact (ArrayTypeDecision.array_type_success_iff_result
              c x (.ArrayT yt) finish finish).2 ⟨harray, rfl⟩
          · exact (UnpackedFieldDecision.unpacked_field_success_iff_result
              yt (UnpackedFieldDecision.unpackedFieldResult yt)
              finish finish).2 ⟨rfl, rfl⟩
  · rintro ⟨yt, t, dt, middle, harrayCall, hunpackCall, hget, hiit⟩
    obtain ⟨harray, hmiddle⟩ :=
      (ArrayTypeDecision.array_type_success_iff_result
        c x (.ArrayT yt) start middle).1 harrayCall
    obtain ⟨ht, hfinish⟩ :=
      (UnpackedFieldDecision.unpacked_field_success_iff_result
        yt t middle finish).1 hunpackCall
    subst t
    subst iit
    exact ⟨by simp [arrayFixedResult, harray, hget],
      hfinish.trans hmiddle⟩

def constantInstructionResult (c : SpecTec.context)
    (irt : SpecTec.inferresulttype) (i : SpecTec.instr) :
    Option SpecTec.inferinstrtype :=
  if ConstSyntaxDecision.syntaxAllowed c i then
    match i with
    | .CONST v => numericLiteralResult v
    | .«VEC.CONST» _ => some vectorLiteralResult
    | .«REF.NULL» ht => refNullResult c ht
    | .«REF.FUNC» x => refFuncResult c x
    | .«GLOBAL.GET» x => globalGetResult c x
    | .«REF.I31» => some i31Result
    | .«STRUCT.NEW» x .Implicit => structImplicitResult c x
    | .«STRUCT.NEW» x .Explicit => structExplicitResult c x
    | .«ARRAY.NEW» x .Implicit => arrayImplicitResult c x
    | .«ARRAY.NEW» x .Explicit => arrayExplicitResult c x
    | .«ARRAY.NEW_FIXED» x count => arrayFixedResult c x count
    | .«EXTERN.CONVERT» op => externConvertResult op irt
    | .BINOP op => arithmeticResult op
    | _ => none
  else none

theorem constant_instruction_result_iff_of_allowed
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (i : SpecTec.instr) (iit : SpecTec.inferinstrtype)
    (start finish : Nat)
    (hallowed : ConstSyntaxDecision.syntaxAllowed c i = true) :
    constantInstructionResult c irt i = some iit ∧ finish = start ↔
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.inferinstrtype,
          SpecTec.SpecTecCall.Instr_ok c irt i⟩)
        start (.success (.of iit)) finish := by
  have hsyntax :=
    (ConstSyntaxDecision.syntaxAllowed_iff c i).1 hallowed
  cases hsyntax with
  | arithmetic i hm =>
      have ⟨op, hi⟩ : ∃ op : SpecTec.binop_,
          i = SpecTec.instr.BINOP op := by
        simp [ConstArithmeticValidation.arithmeticOps] at hm
        rcases hm with h | h | h | h | h | h
        all_goals subst i
        all_goals exact ⟨_, rfl⟩
      subst i
      simpa [constantInstructionResult, hallowed] using
        (arithmetic_result_iff c irt op iit start finish)
  | num v =>
      simpa [constantInstructionResult, hallowed] using
        (numeric_literal_result_iff c irt v iit start finish)
  | vec v =>
      simpa [constantInstructionResult, hallowed] using
        (vector_literal_result_iff c irt v iit start finish)
  | refNull ht =>
      simpa [constantInstructionResult, hallowed] using
        (ref_null_result_iff c irt ht iit start finish)
  | refFunc x =>
      simpa [constantInstructionResult, hallowed] using
        (ref_func_result_iff c irt x iit start finish)
  | refI31 =>
      simpa [constantInstructionResult, hallowed] using
        (i31_result_iff c irt iit start finish)
  | structNew x op =>
      cases op with
      | Implicit =>
          simpa [constantInstructionResult, hallowed] using
            (struct_implicit_result_iff c irt x iit start finish)
      | Explicit =>
          simpa [constantInstructionResult, hallowed] using
            (struct_explicit_result_iff c irt x iit start finish)
  | arrayNew x op =>
      cases op with
      | Implicit =>
          simpa [constantInstructionResult, hallowed] using
            (array_implicit_result_iff c irt x iit start finish)
      | Explicit =>
          simpa [constantInstructionResult, hallowed] using
            (array_explicit_result_iff c irt x iit start finish)
  | arrayNewFixed x count =>
      simpa [constantInstructionResult, hallowed] using
        (array_fixed_result_iff c irt x count iit start finish)
  | externConvert op =>
      simpa [constantInstructionResult, hallowed] using
        (extern_convert_result_iff c irt op iit start finish)
  | globalGet x t hget =>
      simpa [constantInstructionResult, hallowed] using
        (global_get_result_iff c irt x iit start finish)

theorem constant_instruction_result_iff
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (i : SpecTec.instr) (iit : SpecTec.inferinstrtype)
    (start finish : Nat) :
    constantInstructionResult c irt i = some iit ∧ finish = start ↔
      ConstSyntaxDecision.syntaxAllowed c i = true ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.inferinstrtype,
          SpecTec.SpecTecCall.Instr_ok c irt i⟩)
        start (.success (.of iit)) finish := by
  by_cases hallowed : ConstSyntaxDecision.syntaxAllowed c i = true
  · simp only [hallowed, true_and]
    exact constant_instruction_result_iff_of_allowed
      c irt i iit start finish hallowed
  · simp [constantInstructionResult, hallowed]

theorem syntax_instruction_input_shape
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (i : SpecTec.instr) (iit : SpecTec.inferinstrtype)
    (start finish : Nat)
    (hsyntax : ConstAdditionalSyntaxValidation.Syntax c i)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.SpecTecCall.Instr_ok c irt i⟩)
      start (.success (.of iit)) finish) :
    ∃ need : List SpecTec.valtype,
      iit.1.INS = (.NoEllipses, need) ∧ iit.2 = [] := by
  cases hsyntax with
  | arithmetic i hm =>
      simp only [ConstArithmeticValidation.arithmeticOps,
        List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with heq | heq | heq | heq | heq | heq <;> subst i <;>
        obtain ⟨nt, _, heffect⟩ :=
          (ConstNumericBinopDispatch.numeric_binop_dispatch_iff
            c irt _ iit start finish).1 hcall <;>
        rw [heffect] <;>
        exact ⟨_, rfl, rfl⟩
  | num v =>
      obtain ⟨heffect, _⟩ :=
        ConstLiteralDispatch.const_literal_effect c irt v iit start finish hcall
      rw [heffect]
      exact ⟨_, rfl, rfl⟩
  | vec v =>
      obtain ⟨heffect, _⟩ :=
        ConstVectorDispatch.vec_literal_effect c irt v iit start finish hcall
      rw [heffect]
      exact ⟨_, rfl, rfl⟩
  | refNull ht =>
      obtain ⟨_, heffect, _⟩ :=
        (ConstRefNullDispatch.ref_null_dispatch_iff
          c irt ht iit start finish).1 hcall
      rw [heffect]
      exact ⟨_, rfl, rfl⟩
  | refFunc x =>
      obtain ⟨dt, _, _, heffect, _⟩ :=
        (ConstRefFuncEffect.ref_func_instruction_iff
          c irt x iit start finish).1 hcall
      rw [heffect]
      exact ⟨_, rfl, rfl⟩
  | refI31 =>
      obtain ⟨heffect, _⟩ :=
        ConstI31Dispatch.i31_instruction_effect c irt iit start finish hcall
      rw [heffect]
      exact ⟨_, rfl, rfl⟩
  | structNew x op =>
      cases op with
      | Implicit =>
          obtain ⟨_, dt, _, _, _, _, heffect⟩ :=
            (ConstStructImplicitDispatch.struct_new_implicit_dispatch_iff
              c irt x iit start finish).1 hcall
          rw [heffect]
          exact ⟨_, rfl, rfl⟩
      | Explicit =>
          obtain ⟨_, _, dt, _, _, _, _, heffect⟩ :=
            (ConstStructExplicitDispatch.struct_new_explicit_dispatch_iff
              c irt x iit start finish).1 hcall
          rw [heffect]
          exact ⟨_, rfl, rfl⟩
  | arrayNew x op =>
      cases op with
      | Implicit =>
          obtain ⟨_, _, dt, _, _, _, _, _, _, heffect⟩ :=
            (ConstArrayImplicitDispatch.array_new_implicit_dispatch_iff
              c irt x iit start finish).1 hcall
          rw [heffect]
          exact ⟨_, rfl, rfl⟩
      | Explicit =>
          obtain ⟨_, _, dt, _, _, _, _, heffect⟩ :=
            (ConstArrayExplicitDispatch.array_new_explicit_dispatch_iff
              c irt x iit start finish).1 hcall
          rw [heffect]
          exact ⟨_, rfl, rfl⟩
  | arrayNewFixed x count =>
      obtain ⟨_, _, dt, _, _, _, _, heffect⟩ :=
        (ConstArrayFixedDispatch.array_new_fixed_dispatch_iff
          c irt x count iit start finish).1 hcall
      rw [heffect]
      exact ⟨_, rfl, rfl⟩
  | externConvert op =>
      obtain ⟨_, ht2, nu, _, _, _, _, heffect⟩ :=
        (ConstExternConvertDispatch.extern_convert_dispatch_iff
          c irt op iit start finish).1 hcall
      rw [heffect]
      exact ⟨_, rfl, rfl⟩
  | globalGet x t hget =>
      obtain ⟨_, actual, _, heffect, _⟩ :=
        (ConstGlobalGetDispatch.global_get_dispatch_iff
          c irt x iit start finish).1 hcall
      rw [heffect]
      exact ⟨_, rfl, rfl⟩

theorem constant_instruction_input_shape
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (i : SpecTec.instr) (iit : SpecTec.inferinstrtype)
    (h : constantInstructionResult c irt i = some iit) :
    ∃ need : List SpecTec.valtype,
      iit.1.INS = (.NoEllipses, need) ∧ iit.2 = [] := by
  obtain ⟨hallowed, hcall⟩ :=
    (constant_instruction_result_iff c irt i iit 0 0).1 ⟨h, rfl⟩
  exact syntax_instruction_input_shape c irt i iit 0 0
    ((ConstSyntaxDecision.syntaxAllowed_iff c i).1 hallowed) hcall

end properties.wasm_module_ok.ConstInstrDecision
