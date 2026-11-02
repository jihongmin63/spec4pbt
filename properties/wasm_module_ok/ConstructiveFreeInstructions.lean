import properties.wasm_module_ok.ConstructiveFreeTypes
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace properties.wasm_module_ok.ConstructiveFreeInstructions
open SpecTec SpecTecExecution
open properties.wasm_module_ok
open properties.wasm_module_not_ok.Rejection
open FreeUnionValidation properties.wasm_module_ok.ConstructiveFreeTypes

/-- Exact on every original constant instruction; the syntax premise below
excludes control instructions. This is reference computation, not validation. -/
def instrFree : instr → free
  | .«REF.NULL» ht => heaptypeFree ht
  | .«REF.FUNC» x => {emptyFree with FUNCS := .«`{ % `}» [x]}
  | .«GLOBAL.GET» x => {emptyFree with GLOBALS := .«`{ % `}» [x]}
  | .«STRUCT.NEW» x _ | .«ARRAY.NEW» x _ | .«ARRAY.NEW_FIXED» x _ =>
      {emptyFree with TYPES := .«`{ % `}» [x]}
  | _ => emptyFree

macro "reject_free_instr" : tactic => `(tactic|
  (simp only [SpecTec.«$free_instr:clause:0», SpecTec.«$free_instr:clause:1», SpecTec.«$free_instr:clause:2», SpecTec.«$free_instr:clause:3», SpecTec.«$free_instr:clause:4», SpecTec.«$free_instr:clause:5», SpecTec.«$free_instr:clause:6», SpecTec.«$free_instr:clause:7», SpecTec.«$free_instr:clause:8», SpecTec.«$free_instr:clause:9», SpecTec.«$free_instr:clause:10», SpecTec.«$free_instr:clause:11», SpecTec.«$free_instr:clause:12», SpecTec.«$free_instr:clause:13», SpecTec.«$free_instr:clause:14», SpecTec.«$free_instr:clause:15», SpecTec.«$free_instr:clause:16», SpecTec.«$free_instr:clause:17», SpecTec.«$free_instr:clause:18», SpecTec.«$free_instr:clause:19», SpecTec.«$free_instr:clause:20», SpecTec.«$free_instr:clause:21», SpecTec.«$free_instr:clause:22», SpecTec.«$free_instr:clause:23», SpecTec.«$free_instr:clause:24», SpecTec.«$free_instr:clause:25», SpecTec.«$free_instr:clause:26», SpecTec.«$free_instr:clause:27», SpecTec.«$free_instr:clause:28», SpecTec.«$free_instr:clause:29», SpecTec.«$free_instr:clause:30», SpecTec.«$free_instr:clause:31», SpecTec.«$free_instr:clause:32», SpecTec.«$free_instr:clause:33», SpecTec.«$free_instr:clause:34», SpecTec.«$free_instr:clause:35», SpecTec.«$free_instr:clause:36», SpecTec.«$free_instr:clause:37», SpecTec.«$free_instr:clause:38», SpecTec.«$free_instr:clause:39», SpecTec.«$free_instr:clause:40», SpecTec.«$free_instr:clause:41», SpecTec.«$free_instr:clause:42», SpecTec.«$free_instr:clause:43», SpecTec.«$free_instr:clause:44», SpecTec.«$free_instr:clause:45», SpecTec.«$free_instr:clause:46», SpecTec.«$free_instr:clause:47», SpecTec.«$free_instr:clause:48», SpecTec.«$free_instr:clause:49», SpecTec.«$free_instr:clause:50», SpecTec.«$free_instr:clause:51», SpecTec.«$free_instr:clause:52», SpecTec.«$free_instr:clause:53», SpecTec.«$free_instr:clause:54», SpecTec.«$free_instr:clause:55», SpecTec.«$free_instr:clause:56», SpecTec.«$free_instr:clause:57», SpecTec.«$free_instr:clause:58», SpecTec.«$free_instr:clause:59», SpecTec.«$free_instr:clause:60», SpecTec.«$free_instr:clause:61», SpecTec.«$free_instr:clause:62», SpecTec.«$free_instr:clause:63», SpecTec.«$free_instr:clause:64», SpecTec.«$free_instr:clause:65», SpecTec.«$free_instr:clause:66», SpecTec.«$free_instr:clause:67», SpecTec.«$free_instr:clause:68», SpecTec.«$free_instr:clause:69», SpecTec.«$free_instr:clause:70», SpecTec.«$free_instr:clause:71», SpecTec.«$free_instr:clause:72», SpecTec.«$free_instr:clause:73», SpecTec.«$free_instr:clause:74», SpecTec.«$free_instr:clause:75», SpecTec.«$free_instr:clause:76», SpecTec.«$free_instr:clause:77», SpecTec.«$free_instr:clause:78», SpecTec.«$free_instr:clause:79»]
   apply Eval.bind_unmatch
   apply Eval.guard_false
   simp [SpecTec.«exec:match:instr:ARRAY.COPY», SpecTec.«exec:match:instr:ARRAY.FILL», SpecTec.«exec:match:instr:ARRAY.GET», SpecTec.«exec:match:instr:ARRAY.INIT_DATA», SpecTec.«exec:match:instr:ARRAY.INIT_ELEM», SpecTec.«exec:match:instr:ARRAY.LEN», SpecTec.«exec:match:instr:ARRAY.NEW_DATA», SpecTec.«exec:match:instr:ARRAY.NEW_ELEM», SpecTec.«exec:match:instr:ARRAY.NEW_FIXED», SpecTec.«exec:match:instr:ARRAY.NEW», SpecTec.«exec:match:instr:ARRAY.SET», SpecTec.«exec:match:instr:BINOP», SpecTec.«exec:match:instr:BLOCK», SpecTec.«exec:match:instr:BR_IF», SpecTec.«exec:match:instr:BR_ON_CAST_FAIL», SpecTec.«exec:match:instr:BR_ON_CAST», SpecTec.«exec:match:instr:BR_ON_NON_NULL», SpecTec.«exec:match:instr:BR_ON_NULL», SpecTec.«exec:match:instr:BR_TABLE», SpecTec.«exec:match:instr:BR», SpecTec.«exec:match:instr:CALL_INDIRECT», SpecTec.«exec:match:instr:CALL_REF», SpecTec.«exec:match:instr:CALL», SpecTec.«exec:match:instr:COMPARE», SpecTec.«exec:match:instr:CONST», SpecTec.«exec:match:instr:CONVERT», SpecTec.«exec:match:instr:DATA.DROP», SpecTec.«exec:match:instr:DROP», SpecTec.«exec:match:instr:ELEM.DROP», SpecTec.«exec:match:instr:EXTERN.CONVERT», SpecTec.«exec:match:instr:GLOBAL.GET», SpecTec.«exec:match:instr:GLOBAL.SET», SpecTec.«exec:match:instr:I31.GET», SpecTec.«exec:match:instr:IF % % ELSE %», SpecTec.«exec:match:instr:LOAD», SpecTec.«exec:match:instr:LOCAL.GET», SpecTec.«exec:match:instr:LOCAL.SET», SpecTec.«exec:match:instr:LOCAL.TEE», SpecTec.«exec:match:instr:LOOP», SpecTec.«exec:match:instr:MEMORY.COPY», SpecTec.«exec:match:instr:MEMORY.FILL», SpecTec.«exec:match:instr:MEMORY.GROW», SpecTec.«exec:match:instr:MEMORY.INIT», SpecTec.«exec:match:instr:MEMORY.SIZE», SpecTec.«exec:match:instr:NOP», SpecTec.«exec:match:instr:REF.AS_NON_NULL», SpecTec.«exec:match:instr:REF.CAST», SpecTec.«exec:match:instr:REF.EQ», SpecTec.«exec:match:instr:REF.FUNC», SpecTec.«exec:match:instr:REF.I31», SpecTec.«exec:match:instr:REF.IS_NULL», SpecTec.«exec:match:instr:REF.NULL», SpecTec.«exec:match:instr:REF.TEST», SpecTec.«exec:match:instr:RETURN_CALL_INDIRECT», SpecTec.«exec:match:instr:RETURN_CALL_REF», SpecTec.«exec:match:instr:RETURN_CALL», SpecTec.«exec:match:instr:RETURN», SpecTec.«exec:match:instr:SELECT», SpecTec.«exec:match:instr:STORE», SpecTec.«exec:match:instr:STRUCT.GET», SpecTec.«exec:match:instr:STRUCT.NEW», SpecTec.«exec:match:instr:STRUCT.SET», SpecTec.«exec:match:instr:TABLE.COPY», SpecTec.«exec:match:instr:TABLE.FILL», SpecTec.«exec:match:instr:TABLE.GET», SpecTec.«exec:match:instr:TABLE.GROW», SpecTec.«exec:match:instr:TABLE.INIT», SpecTec.«exec:match:instr:TABLE.SET», SpecTec.«exec:match:instr:TABLE.SIZE», SpecTec.«exec:match:instr:TEST», SpecTec.«exec:match:instr:THROW_REF», SpecTec.«exec:match:instr:THROW», SpecTec.«exec:match:instr:TRY_TABLE», SpecTec.«exec:match:instr:UNARY», SpecTec.«exec:match:instr:UNREACHABLE», SpecTec.«exec:match:instr:VEC.LOAD_LANE», SpecTec.«exec:match:instr:VEC.LOAD», SpecTec.«exec:match:instr:VEC.STORE_LANE», SpecTec.«exec:match:instr:VEC.STORE»]))

theorem update_globals_total (xs : List Nat) (n : Nat) :
    Eval Body (.call ⟨free, Call.«$update_globals» (.«`{ % `}» xs)⟩)
      n (.success (.of {emptyFree with GLOBALS := .«`{ % `}» xs})) n := by
  apply Eval.call
  change Eval Body (tryClauses (SpecTec.«$update_globals_clauses» _)) _ _ _
  apply tryClauses_cons_success
  unfold SpecTec.«$update_globals:clause:0»
  apply Eval.bind_success (free_empty_total n)
  exact Eval.pure _

theorem refNull_free_total (ht : heaptype) (n : Nat) :
    Eval Body (.call ⟨free, Call.«$free_instr» (.«REF.NULL» ht)⟩)
      n (.success (.of (instrFree (.«REF.NULL» ht)))) n := by
  apply Eval.call
  change Eval Body (tryClauses (SpecTec.«$free_instr_clauses» (.«REF.NULL» ht))) _ _ _
  iterate 50
    apply tryClauses_cons_unmatch
    · reject_free_instr
  apply tryClauses_cons_success
  unfold SpecTec.«$free_instr:clause:50»
  apply Eval.bind_success (Eval.guard_true rfl)
  apply Eval.bind_success (heaptype_free_total ht n)
  exact Eval.pure _

theorem refFunc_free_total (x : Nat) (n : Nat) :
    Eval Body (.call ⟨free, Call.«$free_instr» (.«REF.FUNC» x)⟩)
      n (.success (.of (instrFree (.«REF.FUNC» x)))) n := by
  apply Eval.call
  change Eval Body (tryClauses (SpecTec.«$free_instr_clauses» (.«REF.FUNC» x))) _ _ _
  iterate 51
    apply tryClauses_cons_unmatch
    · reject_free_instr
  apply tryClauses_cons_success
  unfold SpecTec.«$free_instr:clause:51»
  apply Eval.bind_success (Eval.guard_true rfl)
  apply Eval.bind_success (FreeRefsValidation.free_idx_total x n)
  apply Eval.bind_success (FreeRefsValidation.update_funcs_total [x] n)
  exact Eval.pure _

theorem globalGet_free_total (x : Nat) (n : Nat) :
    Eval Body (.call ⟨free, Call.«$free_instr» (.«GLOBAL.GET» x)⟩)
      n (.success (.of (instrFree (.«GLOBAL.GET» x)))) n := by
  apply Eval.call
  change Eval Body (tryClauses (SpecTec.«$free_instr_clauses» (.«GLOBAL.GET» x))) _ _ _
  iterate 28
    apply tryClauses_cons_unmatch
    · reject_free_instr
  apply tryClauses_cons_success
  unfold SpecTec.«$free_instr:clause:28»
  apply Eval.bind_success (Eval.guard_true rfl)
  apply Eval.bind_success (FreeRefsValidation.free_idx_total x n)
  apply Eval.bind_success (update_globals_total [x] n)
  exact Eval.pure _

theorem structNew_free_total (x : Nat) (op : initop_) (n : Nat) :
    Eval Body (.call ⟨free, Call.«$free_instr» (.«STRUCT.NEW» x op)⟩)
      n (.success (.of (instrFree (.«STRUCT.NEW» x op)))) n := by
  apply Eval.call
  change Eval Body (tryClauses (SpecTec.«$free_instr_clauses» (.«STRUCT.NEW» x op))) _ _ _
  iterate 59
    apply tryClauses_cons_unmatch
    · reject_free_instr
  apply tryClauses_cons_success
  unfold SpecTec.«$free_instr:clause:59»
  apply Eval.bind_success (Eval.guard_true rfl)
  apply Eval.bind_success (FreeRefsValidation.free_idx_total x n)
  apply Eval.bind_success (update_types_total [x] n)
  exact Eval.pure _

theorem arrayNew_free_total (x : Nat) (op : initop_) (n : Nat) :
    Eval Body (.call ⟨free, Call.«$free_instr» (.«ARRAY.NEW» x op)⟩)
      n (.success (.of (instrFree (.«ARRAY.NEW» x op)))) n := by
  apply Eval.call
  change Eval Body (tryClauses (SpecTec.«$free_instr_clauses» (.«ARRAY.NEW» x op))) _ _ _
  iterate 62
    apply tryClauses_cons_unmatch
    · reject_free_instr
  apply tryClauses_cons_success
  unfold SpecTec.«$free_instr:clause:62»
  apply Eval.bind_success (Eval.guard_true rfl)
  apply Eval.bind_success (FreeRefsValidation.free_idx_total x n)
  apply Eval.bind_success (update_types_total [x] n)
  exact Eval.pure _

theorem arrayFixed_free_total (x count : Nat) (n : Nat) :
    Eval Body (.call ⟨free, Call.«$free_instr» (.«ARRAY.NEW_FIXED» x count)⟩)
      n (.success (.of (instrFree (.«ARRAY.NEW_FIXED» x count)))) n := by
  apply Eval.call
  change Eval Body (tryClauses (SpecTec.«$free_instr_clauses» (.«ARRAY.NEW_FIXED» x count))) _ _ _
  iterate 63
    apply tryClauses_cons_unmatch
    · reject_free_instr
  apply tryClauses_cons_success
  unfold SpecTec.«$free_instr:clause:63»
  apply Eval.bind_success (Eval.guard_true rfl)
  apply Eval.bind_success (FreeRefsValidation.free_idx_total x n)
  apply Eval.bind_success (update_types_total [x] n)
  exact Eval.pure _

theorem num_free_total (v : num_) (n : Nat) :
    Eval Body (.call ⟨free, Call.«$free_instr» (.«CONST» v)⟩)
      n (.success (.of (instrFree (.«CONST» v)))) n := by
  apply Eval.call
  change Eval Body (tryClauses (SpecTec.«$free_instr_clauses» (.«CONST» v))) _ _ _
  iterate 74
    apply tryClauses_cons_unmatch
    · reject_free_instr
  apply tryClauses_cons_success
  unfold SpecTec.«$free_instr:clause:74»
  apply Eval.bind_success (Eval.guard_true rfl)
  apply Eval.bind_success (free_empty_total n)
  exact Eval.pure _

theorem vec_free_total (v : vec_) (n : Nat) :
    Eval Body (.call ⟨free, Call.«$free_instr» (.«VEC.CONST» v)⟩)
      n (.success (.of (instrFree (.«VEC.CONST» v)))) n := by
  apply Eval.call
  change Eval Body (tryClauses (SpecTec.«$free_instr_clauses» (.«VEC.CONST» v))) _ _ _
  iterate 80
    apply tryClauses_cons_unmatch
    · reject_free_instr
  apply tryClauses_cons_success
  unfold SpecTec.«$free_instr:clause:80»
  apply Eval.bind_success (free_empty_total n)
  exact Eval.pure _

theorem i31_free_total  (n : Nat) :
    Eval Body (.call ⟨free, Call.«$free_instr» (.«REF.I31» )⟩)
      n (.success (.of (instrFree (.«REF.I31» )))) n := by
  apply Eval.call
  change Eval Body (tryClauses (SpecTec.«$free_instr_clauses» (.«REF.I31» ))) _ _ _
  iterate 57
    apply tryClauses_cons_unmatch
    · reject_free_instr
  apply tryClauses_cons_success
  unfold SpecTec.«$free_instr:clause:57»
  apply Eval.bind_success (Eval.guard_true rfl)
  apply Eval.bind_success (free_empty_total n)
  exact Eval.pure _

theorem extern_free_total (op : externop_) (n : Nat) :
    Eval Body (.call ⟨free, Call.«$free_instr» (.«EXTERN.CONVERT» op)⟩)
      n (.success (.of (instrFree (.«EXTERN.CONVERT» op)))) n := by
  apply Eval.call
  change Eval Body (tryClauses (SpecTec.«$free_instr_clauses» (.«EXTERN.CONVERT» op))) _ _ _
  iterate 73
    apply tryClauses_cons_unmatch
    · reject_free_instr
  apply tryClauses_cons_success
  unfold SpecTec.«$free_instr:clause:73»
  apply Eval.bind_success (Eval.guard_true rfl)
  apply Eval.bind_success (free_empty_total n)
  exact Eval.pure _

theorem binop_free_total (op : binop_) (n : Nat) :
    Eval Body (.call ⟨free, Call.«$free_instr» (.«BINOP» op)⟩)
      n (.success (.of (instrFree (.«BINOP» op)))) n := by
  apply Eval.call
  change Eval Body (tryClauses (SpecTec.«$free_instr_clauses» (.«BINOP» op))) _ _ _
  iterate 78
    apply tryClauses_cons_unmatch
    · reject_free_instr
  apply tryClauses_cons_success
  unfold SpecTec.«$free_instr:clause:78»
  apply Eval.bind_success (Eval.guard_true rfl)
  apply Eval.bind_success (free_empty_total n)
  exact Eval.pure _

theorem instr_free_total (c : context) (i : instr) (n : Nat)
    (h : ConstAdditionalSyntaxValidation.Syntax c i) :
    Eval Body (.call ⟨free, Call.«$free_instr» i⟩)
      n (.success (.of (instrFree i))) n := by
  cases h with
  | arithmetic i hi =>
    simp only [ConstArithmeticValidation.arithmeticOps, List.mem_cons,
      List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> exact binop_free_total _ n
  | num v => exact num_free_total v n
  | vec v => exact vec_free_total v n
  | refNull ht => exact refNull_free_total ht n
  | refFunc x => exact refFunc_free_total x n
  | refI31 => exact i31_free_total n
  | structNew x op => exact structNew_free_total x op n
  | arrayNew x op => exact arrayNew_free_total x op n
  | arrayNewFixed x count => exact arrayFixed_free_total x count n
  | externConvert op => exact extern_free_total op n
  | globalGet x t hget => exact globalGet_free_total x n

end properties.wasm_module_ok.ConstructiveFreeInstructions
