import properties.wasm_module_ok.ConstructiveConstTableSeeds
import properties.wasm_module_ok.ConstructiveConstTableMerge
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveConstTableExpand
open SpecTec properties.wasm_module_ok ConstructiveConstTree ConstructiveGenAudit
open properties.wasm_module_ok.ConstructiveConstBuilders properties.wasm_module_ok.ConstructiveConstAggregateBuilders
open properties.wasm_module_ok.ConstructiveConstTableCore properties.wasm_module_ok.ConstructiveConstTableSeeds

private theorem numeric_table (c : context) (t : numtype) : CandidateValMatch.InTableVal c (.NumT t) := by
  intro ht h; cases h
private theorem base_table (c : context) (nu : null) (ht : heaptype)
    (hb : ht∈HeaptypeValidation.baseHeaptypes) : CandidateValMatch.InTableVal c (.RefT (.«% %» nu ht)) := by
  intro x hx
  have he : x=ht := by simpa [ReadyMatchReachability.sourceValHeaptypes] using hx
  subst x; exact .base ht hb

def fromOperands (c : context) (hr : CandidateTypeReady.Ready c)
    (table : List (Entry c)) (need : List valtype)
    (hnt : ∀t∈need,CandidateValMatch.InTableVal c t)
    (u : valtype) (hu : CandidateValMatch.InTableVal c u)
    (build : Operands c need → Typed c u) : List (Entry c) :=
  match operands c hr table need hnt with
  | none => []
  | some g => [⟨u,g.map build,hu⟩]

def i31Entries (c : context) (hr : CandidateTypeReady.Ready c) (table : List (Entry c)) : List (Entry c) :=
  fromOperands c hr table [.NumT .I32T]
    (by intro t h; have he : t=.NumT .I32T := by simpa using h
        subst t; exact numeric_table c .I32T)
    (.RefT (.«% %» .NoNull .I31HT)) (base_table c .NoNull .I31HT (by simp [HeaptypeValidation.baseHeaptypes]))
    (fun args => independentNode c .«REF.I31» _ _ args .refI31
      (fun irt n => ConstI31Dispatch.i31_dispatch_total c irt n))

def arithmeticEntries (c : context) (hr : CandidateTypeReady.Ready c) (table : List (Entry c))
    (op : binop_) (hop : .BINOP op∈ConstArithmeticValidation.arithmeticOps) : List (Entry c) :=
  fromOperands c hr table [.NumT (ConstInstrDecision.arithmeticType op),.NumT (ConstInstrDecision.arithmeticType op)]
    (by intro t h; have he : t=.NumT (ConstInstrDecision.arithmeticType op) := by simpa using h
        subst t; exact numeric_table c _)
    (.NumT (ConstInstrDecision.arithmeticType op)) (numeric_table c _)
    (fun args => independentNode c (.BINOP op) _ _ args (.arithmetic _ hop) (by
      intro irt n
      apply ((ConstInstrDecision.arithmetic_result_iff c irt op _ n n).1 ?_).2
      exact ⟨by simp [ConstInstrDecision.arithmeticResult,hop,effect],rfl⟩))

def allArithmetic (c : context) (hr : CandidateTypeReady.Ready c) (table : List (Entry c)) : List (Entry c) :=
  arithmeticEntries c hr table (.I32 .IAdd) (by simp [ConstArithmeticValidation.arithmeticOps]) ++
  arithmeticEntries c hr table (.I32 .ISub) (by simp [ConstArithmeticValidation.arithmeticOps]) ++
  arithmeticEntries c hr table (.I32 .IMul) (by simp [ConstArithmeticValidation.arithmeticOps]) ++
  arithmeticEntries c hr table (.I64 .IAdd) (by simp [ConstArithmeticValidation.arithmeticOps]) ++
  arithmeticEntries c hr table (.I64 .ISub) (by simp [ConstArithmeticValidation.arithmeticOps]) ++
  arithmeticEntries c hr table (.I64 .IMul) (by simp [ConstArithmeticValidation.arithmeticOps])

def structEntries (c : context) (hr : CandidateTypeReady.Ready c)
    (hn : CandidateNestedReady.nestedTableReady c=true) (table : List (Entry c)) : List (Entry c) :=
  (structIndices c).flatMap fun index =>
    fromOperands c hr table (StructExplicitFieldsDecision.structFieldInputs index.fields)
      (fun t ht => ConstExtendedCandidateReady.struct_field_in_table c hn index.index index.fields t
        (by simp [StructTypeDecision.structTypeResult,index.lookup,index.expansion]) ht)
      (.RefT (.«% %» .NoNull (.DefHT index.definition)))
      (CandidateValMembership.table_definition_in_table c index.definition (List.mem_of_getElem? index.lookup) .NoNull)
      (structExplicit c index)

def repeatOperands (c : context) (u : valtype) (g : Audited (Matched c u)) :
    (n : Nat) → Audited (Operands c (List.replicate n u))
  | 0 => Audited.pure (emptyOperands c)
  | n+1 => g.bind fun x => (repeatOperands c u g n).map (operandsCons c u _ x)

theorem make_replicate (u : valtype) (n : Nat) : MakeValidation.makeResult u n=List.replicate n u := by
  induction n with
  | zero => rfl
  | succ n ih => simp [MakeValidation.makeResult,ih,List.replicate_succ']

def fixedArrays (c : context) (index : ArrayIndex c)
    (g : Audited (Matched c (UnpackedFieldDecision.unpackedFieldResult index.field))) : Entry c :=
  ⟨.RefT (.«% %» .NoNull (.DefHT index.definition)),
    Audited.bind ⟨Gen.arbNat,arbNat_audit⟩ (fun n =>
      (repeatOperands c _ g n).map fun args =>
        arrayFixed c index n ⟨args.trees,args.good,by simpa only [make_replicate] using args.matching⟩),
    CandidateValMembership.table_definition_in_table c index.definition (List.mem_of_getElem? index.lookup) .NoNull⟩

def arrayEntries (c : context) (hr : CandidateTypeReady.Ready c)
    (hn : CandidateNestedReady.nestedTableReady c=true) (table : List (Entry c)) : List (Entry c) :=
  (arrayIndices c).flatMap fun index =>
    let fieldTable := ConstExtendedCandidateReady.array_field_in_table c hn index.index index.field
      (by simp [ArrayTypeDecision.arrayTypeResult,index.lookup,index.expansion])
    let outputTable := CandidateValMembership.table_definition_in_table c index.definition (List.mem_of_getElem? index.lookup) .NoNull
    let explicit := fromOperands c hr table [UnpackedFieldDecision.unpackedFieldResult index.field,.NumT .I32T]
      (by intro t h; rcases List.mem_cons.mp h with rfl|h
          · exact fieldTable
          · have he : t=.NumT .I32T := by simpa using h
            subst t; exact numeric_table c .I32T)
      _ outputTable (arrayExplicit c index)
    let implicit := if hd : DefaultableValidation.defaultable (UnpackedFieldDecision.unpackedFieldResult index.field)=true then
      fromOperands c hr table [.NumT .I32T]
        (by intro t h; have he : t=.NumT .I32T := by simpa using h
            subst t; exact numeric_table c .I32T)
        _ outputTable (arrayImplicit c index hd)
      else []
    let fixed := match operand c hr (UnpackedFieldDecision.unpackedFieldResult index.field) fieldTable table with
      | none => []
      | some g => [fixedArrays c index g]
    explicit ++ implicit ++ fixed

def externEntries (c : context) (hr : CandidateTypeReady.Ready c) (table : List (Entry c))
    (op : externop_) : List (Entry c) :=
  (ConstructiveConstTableMerge.coalesce table).flatMap fun e =>
    match he : e.type with
    | .RefT (.«% %» nu ht) =>
      if hm : CandidateValMatch.candidateValMatch c e.type (.RefT (.«% %» nu (ExternopTypeDecision.typeExternopResult op).1))=true then
        let targetTable := base_table c nu (ExternopTypeDecision.typeExternopResult op).1
          (by cases op <;> simp [ExternopTypeDecision.typeExternopResult,HeaptypeValidation.baseHeaptypes])
        let outputTable := base_table c nu (ExternopTypeDecision.typeExternopResult op).2
          (by cases op <;> simp [ExternopTypeDecision.typeExternopResult,HeaptypeValidation.baseHeaptypes])
        [⟨_,e.values.map (fun tree => externConvert c op nu ht
          ⟨tree.val,tree.property.1,tree.property.2.trans he⟩ (by
            intro n
            apply (MatchResulttypeDecision.match_pairs_iff_resulttype c _ _ n hr
              (by intro t h; have hte : t=e.type := by simpa [he] using h
                  subst t; exact e.inTable)
              (by intro t h; have hte : t=.RefT (.«% %» nu (ExternopTypeDecision.typeExternopResult op).1) := by simpa using h
                  subst t; exact targetTable)).1
            simpa [MatchResulttypeDecision.matchPairs,he] using hm)),outputTable⟩]
      else []
    | .BotT =>
      let targetTable := base_table c .NoNull (ExternopTypeDecision.typeExternopResult op).1
        (by cases op <;> simp [ExternopTypeDecision.typeExternopResult,HeaptypeValidation.baseHeaptypes])
      let outputTable := base_table c .NoNull (ExternopTypeDecision.typeExternopResult op).2
        (by cases op <;> simp [ExternopTypeDecision.typeExternopResult,HeaptypeValidation.baseHeaptypes])
      [⟨_,e.values.map (fun tree => externBottom c op
        ⟨tree.val,tree.property.1,tree.property.2.trans he⟩ (by
          intro n
          apply (MatchResulttypeDecision.match_pairs_iff_resulttype c _ _ n hr
            (by intro t h; have hte : t=.BotT := by simpa using h
                subst t; intro ht hht; cases hht)
            (by intro t h; have hte : t=.RefT (.«% %» .NoNull (ExternopTypeDecision.typeExternopResult op).1) := by simpa using h
                subst t; exact targetTable)).1
          simp [MatchResulttypeDecision.matchPairs,CandidateValMatch.candidateValMatch,MatchValtypeConditional.matchValtypeResult])),outputTable⟩]
    | _ => []

def expand (c : context) (hr : CandidateTypeReady.Ready c)
    (hn : CandidateNestedReady.nestedTableReady c=true) (table : List (Entry c)) : List (Entry c) :=
  i31Entries c hr table ++ allArithmetic c hr table ++ structEntries c hr hn table ++
    arrayEntries c hr hn table ++ externEntries c hr table .Internalize ++ externEntries c hr table .Externalize

def rounds (c : context) (hr : CandidateTypeReady.Ready c)
    (hp : CandidateUniverseReady.Provenance c) (hn : CandidateNestedReady.nestedTableReady c=true) :
    Nat → List (Entry c)
  | 0 => seeds c hp
  | n+1 => let previous := rounds c hr hp hn n
           previous ++ expand c hr hn previous

theorem rounds_nonempty (c : context) (hr : CandidateTypeReady.Ready c)
    (hp : CandidateUniverseReady.Provenance c) (hn : CandidateNestedReady.nestedTableReady c=true) (n : Nat) :
    rounds c hr hp hn n≠[] := by
  induction n with
  | zero => exact seeds_nonempty c hp
  | succ n ih =>
    cases he : rounds c hr hp hn n with
    | nil => exact False.elim (ih he)
    | cons a as => simp [rounds,he]

#print axioms rounds_nonempty
end properties.wasm_module_ok.ConstructiveConstTableExpand
