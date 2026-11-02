import properties.wasm_module_ok.ConstAdditionalSyntaxValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstSyntaxClassification

theorem clause_zero_syntax
    (c : SpecTec.context) (i : SpecTec.instr)
    (n fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:0» c i)
      n (.success (.of true)) fin) :
    ConstAdditionalSyntaxValidation.Syntax c i := by
  unfold SpecTec.«$is_const:clause:0» at h
  cases h with
  | bind_success hguard htail =>
      cases hguard with
      | guard_true hmem =>
          exact .arithmetic i (by simpa [ConstArithmeticValidation.arithmeticOps] using hmem)

theorem clause_1_syntax
    (c : SpecTec.context) (i : SpecTec.instr)
    (n fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:1» c i)
      n (.success (.of true)) fin) :
    ConstAdditionalSyntaxValidation.Syntax c i := by
  unfold SpecTec.«$is_const:clause:1» at h
  cases h with
  | bind_success hguard htail =>
      cases i <;> simp_all [SpecTec.«exec:match:instr:CONST»] <;>
        first
        | exact .num _
        | (cases hguard <;> contradiction)

theorem clause_2_syntax
    (c : SpecTec.context) (i : SpecTec.instr)
    (n fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:2» c i)
      n (.success (.of true)) fin) :
    ConstAdditionalSyntaxValidation.Syntax c i := by
  unfold SpecTec.«$is_const:clause:2» at h
  cases h with
  | bind_success hguard htail =>
      cases i <;> simp_all [SpecTec.«exec:match:instr:VEC.CONST»] <;>
        first
        | exact .vec _
        | (cases hguard <;> contradiction)

theorem clause_3_syntax
    (c : SpecTec.context) (i : SpecTec.instr)
    (n fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:3» c i)
      n (.success (.of true)) fin) :
    ConstAdditionalSyntaxValidation.Syntax c i := by
  unfold SpecTec.«$is_const:clause:3» at h
  cases h with
  | bind_success hguard htail =>
      cases i <;> simp_all [SpecTec.«exec:match:instr:REF.NULL»] <;>
        first
        | exact .refNull _
        | (cases hguard <;> contradiction)

theorem clause_4_syntax
    (c : SpecTec.context) (i : SpecTec.instr)
    (n fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:4» c i)
      n (.success (.of true)) fin) :
    ConstAdditionalSyntaxValidation.Syntax c i := by
  unfold SpecTec.«$is_const:clause:4» at h
  cases h with
  | bind_success hguard htail =>
      cases i <;> simp_all [SpecTec.«exec:match:instr:REF.FUNC»] <;>
        first
        | exact .refFunc _
        | (cases hguard <;> contradiction)

theorem clause_5_syntax
    (c : SpecTec.context) (i : SpecTec.instr)
    (n fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:5» c i)
      n (.success (.of true)) fin) :
    ConstAdditionalSyntaxValidation.Syntax c i := by
  unfold SpecTec.«$is_const:clause:5» at h
  cases h with
  | bind_success hguard htail =>
      cases i <;> simp_all [SpecTec.«exec:match:instr:REF.I31»] <;>
        first
        | exact .refI31 
        | (cases hguard <;> contradiction)

theorem clause_6_syntax
    (c : SpecTec.context) (i : SpecTec.instr)
    (n fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:6» c i)
      n (.success (.of true)) fin) :
    ConstAdditionalSyntaxValidation.Syntax c i := by
  unfold SpecTec.«$is_const:clause:6» at h
  cases h with
  | bind_success hguard htail =>
      cases i <;> simp_all [SpecTec.«exec:match:instr:STRUCT.NEW»] <;>
        first
        | exact .structNew _ _
        | (cases hguard <;> contradiction)

theorem clause_7_syntax
    (c : SpecTec.context) (i : SpecTec.instr)
    (n fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:7» c i)
      n (.success (.of true)) fin) :
    ConstAdditionalSyntaxValidation.Syntax c i := by
  unfold SpecTec.«$is_const:clause:7» at h
  cases h with
  | bind_success hguard htail =>
      cases i <;> simp_all [SpecTec.«exec:match:instr:ARRAY.NEW»] <;>
        first
        | exact .arrayNew _ _
        | (cases hguard <;> contradiction)

theorem clause_8_syntax
    (c : SpecTec.context) (i : SpecTec.instr)
    (n fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:8» c i)
      n (.success (.of true)) fin) :
    ConstAdditionalSyntaxValidation.Syntax c i := by
  unfold SpecTec.«$is_const:clause:8» at h
  cases h with
  | bind_success hguard htail =>
      cases i <;> simp_all [SpecTec.«exec:match:instr:ARRAY.NEW_FIXED»] <;>
        first
        | exact .arrayNewFixed _ _
        | (cases hguard <;> contradiction)

theorem clause_9_syntax
    (c : SpecTec.context) (i : SpecTec.instr)
    (n fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:9» c i)
      n (.success (.of true)) fin) :
    ConstAdditionalSyntaxValidation.Syntax c i := by
  unfold SpecTec.«$is_const:clause:9» at h
  cases h with
  | bind_success hguard htail =>
      cases i <;> simp_all [SpecTec.«exec:match:instr:EXTERN.CONVERT»] <;>
        first
        | exact .externConvert _
        | (cases hguard <;> contradiction)

theorem clause_10_syntax
    (c : SpecTec.context) (i : SpecTec.instr)
    (n fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:10» c i)
      n (.success (.of true)) fin) :
    ConstAdditionalSyntaxValidation.Syntax c i := by
  unfold SpecTec.«$is_const:clause:10» at h
  cases h with
  | bind_success hguard htail =>
      cases i <;> simp_all [SpecTec.«exec:match:instr:GLOBAL.GET»] <;>
        try (cases hguard <;> contradiction)
      case «GLOBAL.GET» x =>
        cases htail with
        | bind_success hbound hrest =>
            cases hget : c.GLOBALS[x]? with
            | none =>
                rw [hget] at hrest
                cases hrest
            | some gt =>
                cases gt with
                | GlobalT m t =>
                    cases m with
                    | Cons =>
                        exact .globalGet x t hget
                    | Var =>
                        rw [hget] at hrest
                        cases hrest with
                        | bind_success hbad _ =>
                            cases hbad with
                            | guard_true heq => cases heq

theorem ordered_call_syntax
    (c : SpecTec.context) (i : SpecTec.instr)
    (n fin : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$is_const» c i⟩)
      n (.success (.of true)) fin) :
    ConstAdditionalSyntaxValidation.Syntax c i := by
  cases hcall with
  | call hbody =>
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$is_const_clauses» c i))
        n (.success (.of true)) fin at hbody
      obtain ⟨idx, hselected⟩ :=
        (SpecTecExecution.tryClauses_success_iff
          (SpecTec.«$is_const_clauses» c i) n
          (.of true) fin).1 hbody
      unfold SpecTec.«$is_const_clauses» at hselected
      cases hselected with
      | here h0 => exact clause_zero_syntax c i n fin h0
      | next _ hselected =>
          cases hselected with
          | here h1 => exact clause_1_syntax c i n fin h1
          | next _ hselected =>
              cases hselected with
              | here h2 => exact clause_2_syntax c i n fin h2
              | next _ hselected =>
                  cases hselected with
                  | here h3 => exact clause_3_syntax c i n fin h3
                  | next _ hselected =>
                      cases hselected with
                      | here h4 => exact clause_4_syntax c i n fin h4
                      | next _ hselected =>
                          cases hselected with
                          | here h5 => exact clause_5_syntax c i n fin h5
                          | next _ hselected =>
                              cases hselected with
                              | here h6 => exact clause_6_syntax c i n fin h6
                              | next _ hselected =>
                                  cases hselected with
                                  | here h7 => exact clause_7_syntax c i n fin h7
                                  | next _ hselected =>
                                      cases hselected with
                                      | here h8 => exact clause_8_syntax c i n fin h8
                                      | next _ hselected =>
                                          cases hselected with
                                          | here h9 => exact clause_9_syntax c i n fin h9
                                          | next _ hselected =>
                                              cases hselected with
                                              | here h10 => exact clause_10_syntax c i n fin h10
                                              | next _ hselected =>
                                                  cases hselected with
                                                  | here h11 => cases h11
                                                  | next _ hselected => cases hselected

theorem is_const_success_iff
    (c : SpecTec.context) (i : SpecTec.instr)
    (n fin : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$is_const» c i⟩)
      n (.success (.of true)) fin ↔
    ConstAdditionalSyntaxValidation.Syntax c i ∧ fin = n := by
  constructor
  · intro hcall
    have hsyntax := ordered_call_syntax c i n fin hcall
    obtain ⟨_, hsupply⟩ :=
      properties.wasm_module_ok.Execution.eval_deterministic hcall
        (ConstAdditionalSyntaxValidation.syntax_is_const c i n hsyntax)
    exact ⟨hsyntax, hsupply⟩
  · rintro ⟨hsyntax, rfl⟩
    exact ConstAdditionalSyntaxValidation.syntax_is_const c i fin hsyntax

end properties.wasm_module_ok.ConstSyntaxClassification
