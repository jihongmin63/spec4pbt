import properties.wasm_module_ok.ConstSyntaxClassification

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstSyntaxDecision

def syntaxAllowed (c : SpecTec.context) (i : SpecTec.instr) : Bool :=
  if i ∈ ConstArithmeticValidation.arithmeticOps then true
  else
    match i with
    | .CONST _ => true
    | .«VEC.CONST» _ => true
    | .«REF.NULL» _ => true
    | .«REF.FUNC» _ => true
    | .«REF.I31» => true
    | .«STRUCT.NEW» _ _ => true
    | .«ARRAY.NEW» _ _ => true
    | .«ARRAY.NEW_FIXED» _ _ => true
    | .«EXTERN.CONVERT» _ => true
    | .«GLOBAL.GET» x =>
        match c.GLOBALS[x]? with
        | some (.GlobalT .Cons _) => true
        | _ => false
    | _ => false

theorem syntaxAllowed_iff (c : SpecTec.context) (i : SpecTec.instr) :
    syntaxAllowed c i = true ↔
      ConstAdditionalSyntaxValidation.Syntax c i := by
  constructor
  · intro h
    by_cases hm : i ∈ ConstArithmeticValidation.arithmeticOps
    · exact .arithmetic i hm
    · simp only [syntaxAllowed, if_neg hm] at h
      cases i <;> simp_all
      case neg.«GLOBAL.GET» x =>
        cases hget : c.GLOBALS[x]? with
        | none => simp [hget] at h
        | some gt =>
            cases gt with
            | GlobalT m t =>
                cases m with
                | Cons => exact .globalGet x t hget
                | Var => simp [hget] at h
      all_goals
        first
        | exact .num _
        | exact .vec _
        | exact .refNull _
        | exact .refFunc _
        | exact .refI31
        | exact .structNew _ _
        | exact .arrayNew _ _
        | exact .arrayNewFixed _ _
        | exact .externConvert _
  · intro h
    cases h with
    | arithmetic i hm => simp [syntaxAllowed, hm]
    | num v => simp [syntaxAllowed, ConstArithmeticValidation.arithmeticOps]
    | vec v => simp [syntaxAllowed, ConstArithmeticValidation.arithmeticOps]
    | refNull ht => simp [syntaxAllowed, ConstArithmeticValidation.arithmeticOps]
    | refFunc x => simp [syntaxAllowed, ConstArithmeticValidation.arithmeticOps]
    | refI31 => simp [syntaxAllowed, ConstArithmeticValidation.arithmeticOps]
    | structNew ti op => simp [syntaxAllowed, ConstArithmeticValidation.arithmeticOps]
    | arrayNew ti op => simp [syntaxAllowed, ConstArithmeticValidation.arithmeticOps]
    | arrayNewFixed ti len => simp [syntaxAllowed, ConstArithmeticValidation.arithmeticOps]
    | externConvert op => simp [syntaxAllowed, ConstArithmeticValidation.arithmeticOps]
    | globalGet x t hget =>
        simp [syntaxAllowed, ConstArithmeticValidation.arithmeticOps, hget]

end properties.wasm_module_ok.ConstSyntaxDecision
