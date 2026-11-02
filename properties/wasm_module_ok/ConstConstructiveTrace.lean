import properties.wasm_module_ok.InstrsValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstConstructiveTrace

/-- The translated `Instrs_ok` sequence with its final local context retained.
Its returned index list is always empty, including after every cons step. -/
inductive Trace : SpecTec.context → SpecTec.inferresulttype →
    List SpecTec.instr → SpecTec.context → SpecTec.inferresulttype →
    Nat → Nat → Prop where
  | nil (c : SpecTec.context) (irt : SpecTec.inferresulttype)
      (n : Nat) : Trace c irt [] c irt n n
  | cons {c next finalContext : SpecTec.context}
      {irt popped pushed finalStack : SpecTec.inferresulttype}
      {i : SpecTec.instr} {rest : List SpecTec.instr}
      {iit : SpecTec.inferinstrtype}
      {n middle₁ middle₂ middle₃ middle₄ finish : Nat}
      (hinstr : SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.inferinstrtype,
          SpecTec.Call.Instr_ok c irt i⟩)
        n (.success (.of iit)) middle₁)
      (hinit : SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.context,
          SpecTec.Call.«$init_locals» c iit.2⟩)
        middle₁ (.success (.of next)) middle₂)
      (hpop : SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.inferresulttype,
          SpecTec.Call.«$pop» c iit.1.INS irt⟩)
        middle₂ (.success (.of popped)) middle₃)
      (hpush : SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.inferresulttype,
          SpecTec.Call.«$push» c iit.1.OUTS popped⟩)
        middle₃ (.success (.of pushed)) middle₄)
      (htail : Trace next pushed rest finalContext finalStack middle₄ finish) :
      Trace c irt (i :: rest) finalContext finalStack n finish

theorem trace_to_instrs
    {c finalContext : SpecTec.context}
    {irt finalStack : SpecTec.inferresulttype}
    {xs : List SpecTec.instr} {start finish : Nat}
    (h : Trace c irt xs finalContext finalStack start finish) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferresulttype × List SpecTec.idx,
        SpecTec.Call.Instrs_ok c irt xs⟩)
      start (.success (.of (finalStack, ([] : List SpecTec.idx)))) finish := by
  induction h with
  | nil c irt n =>
    exact InstrsValidation.instrs_nil_total c irt n
  | @cons c next finalContext irt popped pushed finalStack
      i rest iit n middle₁ middle₂ middle₃ middle₄ finish
      hinstr hinit hpop hpush htail ih =>
    exact (InstrsValidation.instrs_cons_success_iff
      c irt i rest (finalStack, ([] : List SpecTec.idx)) n finish).2
      ⟨iit, next, popped, pushed,
        middle₁, middle₂, middle₃, middle₄,
        hinstr, hinit, hpop, hpush, ih⟩

theorem instrs_to_trace
    (xs : List SpecTec.instr)
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (finalStack : SpecTec.inferresulttype)
    (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferresulttype × List SpecTec.idx,
        SpecTec.Call.Instrs_ok c irt xs⟩)
      start (.success (.of
        (finalStack, ([] : List SpecTec.idx)))) finish) :
    ∃ finalContext : SpecTec.context,
      Trace c irt xs finalContext finalStack start finish := by
  induction xs generalizing c irt start with
  | nil =>
    obtain ⟨hresult, hsupply⟩ :=
      (InstrsValidation.instrs_nil_success_iff
        c irt (finalStack, ([] : List SpecTec.idx)) start finish).1 h
    have hstack : finalStack = irt := congrArg Prod.fst hresult
    subst finalStack
    subst finish
    exact ⟨c, Trace.nil c irt start⟩
  | cons i rest ih =>
    obtain ⟨iit, next, popped, pushed,
      middle₁, middle₂, middle₃, middle₄,
      hinstr, hinit, hpop, hpush, htail⟩ :=
      (InstrsValidation.instrs_cons_success_iff
        c irt i rest (finalStack, ([] : List SpecTec.idx))
        start finish).1 h
    obtain ⟨finalContext, hrest⟩ :=
      ih next pushed middle₄ htail
    exact ⟨finalContext,
      Trace.cons hinstr hinit hpop hpush hrest⟩

/-- Producer and consumer traces concatenate at the producer's actual end
context and stack. No validation is rerun or discarded. -/
theorem trace_append
    {c middle : SpecTec.context}
    {irt middleStack : SpecTec.inferresulttype}
    {xs : List SpecTec.instr} {start middleSupply : Nat}
    (hfirst : Trace c irt xs middle middleStack start middleSupply) :
    ∀ {ys : List SpecTec.instr} {finalContext : SpecTec.context}
      {finalStack : SpecTec.inferresulttype} {finish : Nat},
      Trace middle middleStack ys finalContext finalStack
        middleSupply finish →
      Trace c irt (xs ++ ys) finalContext finalStack start finish := by
  induction hfirst with
  | nil c irt n =>
    intro ys finalContext finalStack finish hsecond
    simpa using hsecond
  | @cons c next middle irt popped pushed middleStack
      i rest iit n middle₁ middle₂ middle₃ middle₄ middleSupply
      hinstr hinit hpop hpush htail ih =>
    intro ys finalContext finalStack finish hsecond
    simpa only [List.cons_append] using
      (Trace.cons hinstr hinit hpop hpush (ih hsecond))

theorem instrs_success_indices_nil
    (xs : List SpecTec.instr)
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (result : SpecTec.inferresulttype × List SpecTec.idx)
    (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferresulttype × List SpecTec.idx,
        SpecTec.Call.Instrs_ok c irt xs⟩)
      start (.success (.of result)) finish) :
    result.2 = [] := by
  induction xs generalizing c irt start with
  | nil =>
    obtain ⟨hresult, _⟩ :=
      (InstrsValidation.instrs_nil_success_iff
        c irt result start finish).1 h
    exact congrArg Prod.snd hresult
  | cons i rest ih =>
    obtain ⟨iit, next, popped, pushed,
      middle₁, middle₂, middle₃, middle₄,
      hinstr, hinit, hpop, hpush, htail⟩ :=
      (InstrsValidation.instrs_cons_success_iff
        c irt i rest result start finish).1 h
    exact ih next pushed middle₄ htail

/-- Exact characterization of any successful translated `Instrs_ok` call by
an annotated trace and its otherwise hidden final local context. -/
theorem instrs_success_iff_trace
    (xs : List SpecTec.instr)
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (result : SpecTec.inferresulttype × List SpecTec.idx)
    (start finish : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferresulttype × List SpecTec.idx,
        SpecTec.Call.Instrs_ok c irt xs⟩)
      start (.success (.of result)) finish ↔
    result.2 = [] ∧
      ∃ finalContext : SpecTec.context,
        Trace c irt xs finalContext result.1 start finish := by
  constructor
  · intro h
    have hindices := instrs_success_indices_nil
      xs c irt result start finish h
    rcases result with ⟨stack, indices⟩
    dsimp at hindices ⊢
    subst indices
    obtain ⟨finalContext, htrace⟩ :=
      instrs_to_trace xs c irt stack start finish h
    exact ⟨rfl, finalContext, htrace⟩
  · rintro ⟨hindices, finalContext, htrace⟩
    rcases result with ⟨stack, indices⟩
    dsimp at hindices ⊢
    subst indices
    exact trace_to_instrs htrace

/-- Append one consumer instruction after an existing producer trace. The
consumer reads the producer's actual ending local context and stack. -/
theorem trace_snoc
    {c middle next : SpecTec.context}
    {irt middleStack popped pushed : SpecTec.inferresulttype}
    {xs : List SpecTec.instr} {i : SpecTec.instr}
    {iit : SpecTec.inferinstrtype}
    {n middleSupply afterInstr afterInit afterPop afterPush : Nat}
    (hfirst : Trace c irt xs middle middleStack n middleSupply)
    (hinstr : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.Call.Instr_ok middle middleStack i⟩)
      middleSupply (.success (.of iit)) afterInstr)
    (hinit : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.«$init_locals» middle iit.2⟩)
      afterInstr (.success (.of next)) afterInit)
    (hpop : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.Call.«$pop» middle iit.1.INS middleStack⟩)
      afterInit (.success (.of popped)) afterPop)
    (hpush : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.Call.«$push» middle iit.1.OUTS popped⟩)
      afterPop (.success (.of pushed)) afterPush) :
    Trace c irt (xs ++ [i]) next pushed n afterPush := by
  exact trace_append hfirst
    (Trace.cons hinstr hinit hpop hpush
      (Trace.nil next pushed afterPush))

end properties.wasm_module_ok.ConstConstructiveTrace
