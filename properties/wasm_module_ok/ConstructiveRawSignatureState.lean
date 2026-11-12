import properties.wasm_module_ok.ConstructiveSignatureState

set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveRawSignatureState
open SpecTec properties.wasm_module_ok
open ConstructiveTypeCopy ConstructiveTypeCopySemantics ConstructiveTypeEnvironment
open ConstructiveSignaturePlan ConstructiveSignatureState ConstructiveTypeSkeletonTrace

def weaken (c d : context) (hle : c.TYPES.length ≤ d.TYPES.length) (s : Signature c) : Signature d :=
  ⟨s.header,s.shape,ConstructiveFreshSignatures.shape_weaken _ _ hle s.shape s.valid,s.agrees⟩

def raw (c : context) (st : SpecTec.subtype) (hv : SubtypeValidation.subtypeValid c st = true) :
    Signature c := by
  cases st with
  | SubT f ps shape =>
    exact ⟨⟨f,kind shape⟩,shape,(ConstructiveVarianceShapes.valid_shape_iff c shape).2 (by
      simp only [SubtypeValidation.subtypeValid,Bool.and_eq_true] at hv
      exact hv.2),rfl⟩

theorem raw_header (c : context) (st : SpecTec.subtype) (hv : SubtypeValidation.subtypeValid c st = true) :
    (raw c st hv).header = header st := by cases st; rfl

theorem raw_headers (c : context) (sts : List SpecTec.subtype)
    (h : ∀ st ∈ sts, SubtypeValidation.subtypeValid c st = true) :
    headers c (mapP _ (raw c) sts h) = sts.map header := by
  induction sts with
  | nil => rfl
  | cons st sts ih =>
    simp only [headers,mapP,List.map_cons,raw_header,List.cons.injEq,true_and]
    exact ih _

def next (c : context) (sts : List SpecTec.subtype)
    (hb : GroupBound (c.TYPES.length+sts.length) sts) (env : List (Signature c))
    (hsource : CandidateSourceChecks.sourceChecks (extended c sts hb) sts = true) :
    List (Signature (extended c sts hb)) :=
  env.map (weaken c (extended c sts hb) (by simp [extended,definitions])) ++
    mapP _ (raw (extended c sts hb)) sts ((ConstructiveTypeCopySource.subs_valid _ _).1 hsource)

theorem next_headers (c : context) (sts : List SpecTec.subtype)
    (hb : GroupBound (c.TYPES.length+sts.length) sts) (env : List (Signature c))
    (hsource : CandidateSourceChecks.sourceChecks (extended c sts hb) sts = true) :
    headers (extended c sts hb) (next c sts hb env hsource) = headers c env ++ sts.map header := by
  unfold next
  rw [show ∀ {c : context} (xs ys : List (Signature c)), headers c (xs++ys)=headers c xs++headers c ys from
    fun xs ys => List.map_append]
  rw [raw_headers]
  simp [headers,weaken,List.map_map,Function.comp_def]

theorem next_tracks (c : context) (sts : List SpecTec.subtype)
    (hb : GroupBound (c.TYPES.length+sts.length) sts) (env : List (Signature c))
    (hsource : CandidateSourceChecks.sourceChecks (extended c sts hb) sts = true)
    (hmeta : Tracks c (headers c env)) :
    Tracks (extended c sts hb) (headers (extended c sts hb) (next c sts hb env hsource)) := by
  rw [next_headers]
  exact ConstructiveTypeMetadata.tracks_closed c (headers c env) sts hb hmeta

theorem raw_at_closed (c : context) (sts : List SpecTec.subtype)
    (hb : GroupBound (c.TYPES.length+sts.length) sts) (i : Nat) (st : SpecTec.subtype)
    (hget : sts[i]? = some st) (hv : SubtypeValidation.subtypeValid (extended c sts hb) st = true) :
    At (extended c sts hb) (c.TYPES.length+i)
      (raw (extended c sts hb) st hv).header.finality (raw (extended c sts hb) st hv).shape := by
  cases st with
  | SubT f ps shape => exact remaining_closed c sts hb i f ps shape hget

theorem next_describes (c : context) (sts : List SpecTec.subtype)
    (hb : GroupBound (c.TYPES.length+sts.length) sts) (env : List (Signature c))
    (hsource : CandidateSourceChecks.sourceChecks (extended c sts hb) sts = true)
    (hlen : env.length = c.TYPES.length) (hd : Describes c c env) :
    Describes (extended c sts hb) (extended c sts hb) (next c sts hb env hsource) := by
  intro p s hs
  by_cases hold : p < env.length
  · have hm : (env.map (weaken c (extended c sts hb) (by simp [extended,definitions])))[p]? = some s := by
      simpa only [next,List.getElem?_append_left (by simpa : p < (env.map
        (weaken c (extended c sts hb) (by simp [extended,definitions]))).length)] using hs
    simp only [List.getElem?_map,Option.map_eq_some_iff] at hm
    obtain ⟨old,hget,rfl⟩ := hm
    exact at_prefix c (extended c sts hb) _ rfl p old.header.finality old.shape (hd p old hget)
  · have hlenMap : (env.map (weaken c (extended c sts hb) (by simp [extended,definitions]))).length = env.length := by simp
    have hp : env.length ≤ p := by omega
    have hg : (mapP _ (raw (extended c sts hb)) sts
        ((ConstructiveTypeCopySource.subs_valid _ _).1 hsource))[p-env.length]? = some s := by
      unfold next at hs
      rw [List.getElem?_append_right (by simpa using hp)] at hs
      simpa only [hlenMap] using hs
    have hi : p-env.length < sts.length := by
      have hm := (List.getElem?_eq_some_iff.mp hg).1
      simpa only [mapP_length] using hm
    have hget := List.getElem?_eq_getElem hi
    let st := sts[p-env.length]
    have hv := (ConstructiveTypeCopySource.subs_valid _ _).1 hsource st (List.mem_of_getElem? hget)
    have hm := mapP_get _ (raw (extended c sts hb)) sts
      ((ConstructiveTypeCopySource.subs_valid _ _).1 hsource) (p-env.length) st hget hv
    have heq : s = raw (extended c sts hb) st hv := Option.some.inj (hg.symm.trans hm)
    rw [heq]
    have hp' : c.TYPES.length+(p-env.length) = p := by omega
    simpa only [hp'] using raw_at_closed c sts hb (p-env.length) st hget hv

end properties.wasm_module_ok.ConstructiveRawSignatureState
