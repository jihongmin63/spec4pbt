import properties.wasm_module_ok.ConstructiveHistoryState
import properties.wasm_module_ok.ConstructiveRawSignatureState

set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveTypesState
open SpecTec properties.wasm_module_ok
open ConstructiveTypeCopy ConstructiveTypeEnvironment ConstructiveSignaturePlan
open ConstructiveSignatureState ConstructiveTypeSkeletonTrace ConstructiveTypeHistory

/-- All next-group preconditions are maintained by construction from the
empty type table. Runtime state consists only of signatures and source history. -/
structure State (c : context) where
  signatures : List (Signature c)
  history : List (Stored c)
  validated : ValidatedTypeChain.ValidatedTypes c
  metadata : Tracks c (headers c signatures)
  denotes : Describes c c signatures
  provenance : Covers c history

def empty (c : context) (hc : c.TYPES = []) : State c where
  signatures := []
  history := []
  validated := .seed c hc
  metadata := by simp [Tracks,headers,headerAt,hc]
  denotes := by intro i s hs; simp at hs
  provenance := by intro p dt hp; simp [hc] at hp

def rawGroups (c : context) (state : State c) : Gen (List SpecTec.subtype) :=
  (fun rt => match rt with | rectype.RecT sts => sts) <$> groups c state.signatures state.history

theorem raw_support (c : context) (state : State c) (sts : List SpecTec.subtype) :
    Gen.support (rawGroups c state) sts ↔
      Gen.support (groups c state.signatures state.history) (.RecT sts) := by
  simp only [rawGroups,Gen.Support.support_map]
  constructor
  · rintro ⟨rt,hg,he⟩
    cases rt with | RecT ss => cases he; exact hg
  · intro hg; exact ⟨.RecT sts,hg,rfl⟩

abbrev Choice (c : context) (state : State c) :=
  {sts : List SpecTec.subtype // Gen.support (groups c state.signatures state.history) (.RecT sts)}

def choose (c : context) (state : State c) : Gen (Choice c state) :=
  ConstructiveAttach.refine (rawGroups c state)
    (by simpa only [rawGroups,ConstructiveGenAudit.map_audit] using groups_audit c state.signatures state.history)
    _ (fun sts hs => (raw_support c state sts).1 hs)

theorem choose_covers (c : context) (state : State c) (x : Choice c state) :
    Gen.support (choose c state) x := by
  rw [choose,ConstructiveAttach.refine_support,raw_support]
  exact x.property

theorem choose_audit (c : context) (state : State c) : ConstructiveGenAudit.Structural (choose c state) :=
  ConstructiveAttach.refine_audit _ _ _ _

theorem bound (c : context) (state : State c) (x : Choice c state) :
    GroupBound (c.TYPES.length+x.val.length) x.val := by
  obtain ⟨out,hout⟩ := groups_sound c state.signatures state.history state.validated state.metadata state.denotes
    (.RecT x.val) x.property 0
  exact ConstructiveTypeCopySource.original_bound c out x.val 0 0 hout

def output (c : context) (state : State c) (x : Choice c state) : context :=
  extended c x.val (bound c state x)

theorem execute (c : context) (state : State c) (x : Choice c state) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨context,SpecTec.Call.Rectype_ok c (.RecT x.val)⟩)
      n (.success (.of (output c state x))) n := by
  obtain ⟨out,hout⟩ := groups_sound c state.signatures state.history state.validated state.metadata state.denotes
    (.RecT x.val) x.property n
  have he := ConstructiveFreshCompleteness.original_closed c out x.val n n hout (bound c state x)
  simpa only [output,he] using hout

theorem source (c : context) (state : State c) (x : Choice c state) :
    CandidateSourceChecks.sourceChecks (output c state x) x.val = true := by
  have he := execute c state x 0
  exact CandidateSourceChecks.rectype_success_sourceChecks c (output c state x) (output c state x) x.val
    0 0 he (CandidateRectypeTable.rectype_success_candidateContext c (output c state x) x.val 0 0 he)

def advance (c : context) (state : State c) (x : Choice c state) : State (output c state x) where
  signatures := ConstructiveRawSignatureState.next c x.val (bound c state x) state.signatures (source c state x)
  history := ConstructiveHistoryState.next c x.val (bound c state x) state.validated 0 (execute c state x 0) state.history
  validated := .append c (output c state x) x.val 0 0 state.validated (execute c state x 0)
  metadata := ConstructiveRawSignatureState.next_tracks c x.val (bound c state x) state.signatures
    (source c state x) state.metadata
  denotes := ConstructiveRawSignatureState.next_describes c x.val (bound c state x) state.signatures
    (source c state x) (by simpa [headers] using state.metadata.1) state.denotes
  provenance := ConstructiveHistoryState.next_covers c x.val (bound c state x) state.validated 0
    (execute c state x 0) state.history state.provenance

theorem original_choice (c result : context) (state : State c) (sts : List SpecTec.subtype)
    (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨context,SpecTec.Call.Rectype_ok c (.RecT sts)⟩)
      start (.success (.of result)) finish) :
    Gen.support (groups c state.signatures state.history) (.RecT sts) :=
  groups_complete c result state.signatures state.history state.validated state.metadata state.denotes
    state.provenance sts start finish h

end properties.wasm_module_ok.ConstructiveTypesState
