import properties.wasm_module_ok.ConstructiveConstOriginalLeaves
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveConstOriginalAggregates
open SpecTec properties.wasm_module_ok ConstructiveConstTree ConstructiveGenAudit
open properties.wasm_module_ok.ConstructiveConstBuilders properties.wasm_module_ok.ConstructiveConstAggregateBuilders
open properties.wasm_module_ok.ConstructiveConstTableCore properties.wasm_module_ok.ConstructiveConstTableSeeds properties.wasm_module_ok.ConstructiveConstTableExpand
open properties.wasm_module_ok.ConstructiveConstTableCoverage properties.wasm_module_ok.ConstructiveConstSeedCoverage properties.wasm_module_ok.ConstructiveConstExpansionCoverage
open properties.wasm_module_ok.ConstructiveConstFixedCoverage properties.wasm_module_ok.ConstructiveConstOriginalLeaves

theorem struct_expansion (c : context) (x : Nat) (dt : deftype) (fields : List fieldtype)
    (hget : c.TYPES[x]?=some dt)
    (hs : StructTypeDecision.structTypeResult c x=some (.StructT fields)) :
    UnrollInterface.expandResult dt=some (.DefStructT (.StructT fields)) := by
  cases he : UnrollInterface.expandResult dt with
  | none => simp [StructTypeDecision.structTypeResult,hget,he] at hs
  | some st =>
    cases st with
    | DefStructT st =>
      have hst : st=.StructT fields := by simpa [StructTypeDecision.structTypeResult,hget,he] using hs
      simpa only [hst] using he
    | DefArrayT _ => simp [StructTypeDecision.structTypeResult,hget,he] at hs
    | DefFuncT _ => simp [StructTypeDecision.structTypeResult,hget,he] at hs

theorem array_expansion (c : context) (x : Nat) (dt : deftype) (field : fieldtype)
    (hget : c.TYPES[x]?=some dt)
    (hs : ArrayTypeDecision.arrayTypeResult c x=some (.ArrayT field)) :
    UnrollInterface.expandResult dt=some (.DefArrayT (.ArrayT field)) := by
  cases he : UnrollInterface.expandResult dt with
  | none => simp [ArrayTypeDecision.arrayTypeResult,hget,he] at hs
  | some st =>
    cases st with
    | DefArrayT st =>
      have hst : st=.ArrayT field := by simpa [ArrayTypeDecision.arrayTypeResult,hget,he] using hs
      simpa only [hst] using he
    | DefStructT _ => simp [ArrayTypeDecision.arrayTypeResult,hget,he] at hs
    | DefFuncT _ => simp [ArrayTypeDecision.arrayTypeResult,hget,he] at hs

theorem struct_explicit_node (c : context) (hr : CandidateTypeReady.Ready c)
    (hn : CandidateNestedReady.nestedTableReady c=true) (table : List (Entry c))
    (x : Nat) (u : valtype) (children : List Tree) (need : List valtype)
    (hi : ConstInstrDecision.structExplicitResult c x=some (effect need u))
    (hm : ∀n,SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,Call.Match_resulttype c (outputs children) need⟩)
      n (.success (.of ())) n)
    (hk : ∀t∈children,Good c t) (hc : ∀t∈children,Covers table t) :
    Covers (structEntries c hr hn table) (.node (.«STRUCT.NEW» x .Explicit) u children) := by
  cases hs : StructTypeDecision.structTypeResult c x with
  | none => simp [ConstInstrDecision.structExplicitResult,hs] at hi
  | some st =>
    cases st with
    | StructT fields =>
      cases hg : c.TYPES[x]? with
      | none => simp [ConstInstrDecision.structExplicitResult,hg] at hi
      | some dt =>
        have he : effect (StructExplicitFieldsDecision.structFieldInputs fields) (.RefT (.«% %» .NoNull (.DefHT dt)))=effect need u := by
          simpa [ConstInstrDecision.structExplicitResult,hs,hg,effect] using hi
        obtain ⟨hneed,hout⟩ := effect_inj _ _ _ _ he
        subst need; subst u
        exact struct_cover c hr hn table ⟨x,dt,fields,hg,struct_expansion c x dt fields hg hs⟩ ⟨children,hk,hm⟩ hc

theorem struct_implicit_node (c : context) (hp : CandidateUniverseReady.Provenance c)
    (x : Nat) (u : valtype) (children : List Tree) (need : List valtype)
    (hi : ConstInstrDecision.structImplicitResult c x=some (effect need u))
    (hm : ∀n,SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,Call.Match_resulttype c (outputs children) need⟩)
      n (.success (.of ())) n) :
    Covers (implicitStructEntries c hp) (.node (.«STRUCT.NEW» x .Implicit) u children) := by
  cases hs : StructTypeDecision.structTypeResult c x with
  | none => simp [ConstInstrDecision.structImplicitResult,hs] at hi
  | some st =>
    cases st with
    | StructT fields =>
      cases hg : c.TYPES[x]? with
      | none => simp [ConstInstrDecision.structImplicitResult,hg] at hi
      | some dt =>
        by_cases hd : StructImplicitFieldsDecision.structFieldsDefaultable fields=true
        · have he : effect [] (.RefT (.«% %» .NoNull (.DefHT dt)))=effect need u := by
            simpa [ConstInstrDecision.structImplicitResult,hs,hg,hd,effect] using hi
          obtain ⟨hneed,hout⟩ := effect_inj _ _ _ _ he
          subst need; subst u
          have hch := empty_children c children (hm 0)
          subst children
          exact implicit_struct_cover c hp ⟨x,dt,fields,hg,struct_expansion c x dt fields hg hs⟩ hd
        · simp [ConstInstrDecision.structImplicitResult,hs,hg,hd] at hi

theorem array_explicit_node (c : context) (hr : CandidateTypeReady.Ready c)
    (hn : CandidateNestedReady.nestedTableReady c=true) (table : List (Entry c))
    (x : Nat) (u : valtype) (children : List Tree) (need : List valtype)
    (hi : ConstInstrDecision.arrayExplicitResult c x=some (effect need u))
    (hm : ∀n,SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,Call.Match_resulttype c (outputs children) need⟩)
      n (.success (.of ())) n)
    (hk : ∀t∈children,Good c t) (hc : ∀t∈children,Covers table t) :
    Covers (arrayEntries c hr hn table) (.node (.«ARRAY.NEW» x .Explicit) u children) := by
  cases hs : ArrayTypeDecision.arrayTypeResult c x with
  | none => simp [ConstInstrDecision.arrayExplicitResult,hs] at hi
  | some st =>
    cases st with
    | ArrayT field =>
      cases hg : c.TYPES[x]? with
      | none => simp [ConstInstrDecision.arrayExplicitResult,hg] at hi
      | some dt =>
        have he : effect [UnpackedFieldDecision.unpackedFieldResult field,.NumT .I32T] (.RefT (.«% %» .NoNull (.DefHT dt)))=effect need u := by
          simpa [ConstInstrDecision.arrayExplicitResult,hs,hg,effect] using hi
        obtain ⟨hneed,hout⟩ := effect_inj _ _ _ _ he
        subst need; subst u
        exact array_explicit_cover c hr hn table ⟨x,dt,field,hg,array_expansion c x dt field hg hs⟩ ⟨children,hk,hm⟩ hc

theorem array_implicit_node (c : context) (hr : CandidateTypeReady.Ready c)
    (hn : CandidateNestedReady.nestedTableReady c=true) (table : List (Entry c))
    (x : Nat) (u : valtype) (children : List Tree) (need : List valtype)
    (hi : ConstInstrDecision.arrayImplicitResult c x=some (effect need u))
    (hm : ∀n,SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,Call.Match_resulttype c (outputs children) need⟩)
      n (.success (.of ())) n)
    (hk : ∀t∈children,Good c t) (hc : ∀t∈children,Covers table t) :
    Covers (arrayEntries c hr hn table) (.node (.«ARRAY.NEW» x .Implicit) u children) := by
  cases hs : ArrayTypeDecision.arrayTypeResult c x with
  | none => simp [ConstInstrDecision.arrayImplicitResult,hs] at hi
  | some st =>
    cases st with
    | ArrayT field =>
      cases hg : c.TYPES[x]? with
      | none => simp [ConstInstrDecision.arrayImplicitResult,hg] at hi
      | some dt =>
        by_cases hd : DefaultableValidation.defaultable (UnpackedFieldDecision.unpackedFieldResult field)=true
        · have he : effect [.NumT .I32T] (.RefT (.«% %» .NoNull (.DefHT dt)))=effect need u := by
            simpa [ConstInstrDecision.arrayImplicitResult,hs,hg,hd,effect] using hi
          obtain ⟨hneed,hout⟩ := effect_inj _ _ _ _ he
          subst need; subst u
          exact array_implicit_cover c hr hn table ⟨x,dt,field,hg,array_expansion c x dt field hg hs⟩ hd ⟨children,hk,hm⟩ hc
        · simp [ConstInstrDecision.arrayImplicitResult,hs,hg,hd] at hi

theorem array_fixed_node (c : context) (hr : CandidateTypeReady.Ready c)
    (hp : CandidateUniverseReady.Provenance c)
    (hn : CandidateNestedReady.nestedTableReady c=true) (table : List (Entry c))
    (x count : Nat) (u : valtype) (children : List Tree) (need : List valtype)
    (hi : ConstInstrDecision.arrayFixedResult c x count=some (effect need u))
    (hm : ∀n,SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,Call.Match_resulttype c (outputs children) need⟩)
      n (.success (.of ())) n)
    (hk : ∀t∈children,Good c t) (hc : ∀t∈children,Covers table t) :
    Covers (emptyArrayEntries c hp ++ arrayEntries c hr hn table) (.node (.«ARRAY.NEW_FIXED» x count) u children) := by
  cases hs : ArrayTypeDecision.arrayTypeResult c x with
  | none => simp [ConstInstrDecision.arrayFixedResult,hs] at hi
  | some st =>
    cases st with
    | ArrayT field =>
      cases hg : c.TYPES[x]? with
      | none => simp [ConstInstrDecision.arrayFixedResult,hg] at hi
      | some dt =>
        have he : effect (MakeValidation.makeResult (UnpackedFieldDecision.unpackedFieldResult field) count) (.RefT (.«% %» .NoNull (.DefHT dt)))=effect need u := by
          simpa [ConstInstrDecision.arrayFixedResult,hs,hg,effect] using hi
        obtain ⟨hneed,hout⟩ := effect_inj _ _ _ _ he
        subst need; subst u
        let index : ArrayIndex c := ⟨x,dt,field,hg,array_expansion c x dt field hg hs⟩
        by_cases hcount : count=0
        · subst count
          have hch := empty_children c children (hm 0)
          subst children
          exact covers_mono (fun _ h => List.mem_append_left _ h) (empty_array_cover c hp index)
        · exact covers_mono (fun _ h => List.mem_append_right _ h)
            (array_fixed_cover c hr hn table index count hcount ⟨children,hk,hm⟩ hc)

#print axioms array_fixed_node
end properties.wasm_module_ok.ConstructiveConstOriginalAggregates
