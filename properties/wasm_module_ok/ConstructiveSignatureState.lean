import properties.wasm_module_ok.ConstructiveFreshSignatures
import properties.wasm_module_ok.ConstructiveTypeNested
import properties.wasm_module_ok.ConstructiveTypeCopyPrefix

set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveSignatureState
open SpecTec properties.wasm_module_ok
open properties.wasm_module_not_ok.Rejection
open ConstructiveSignaturePlan ConstructiveTypeSkeleton ConstructiveTypeSkeletonTrace
open ConstructiveTypeCopyRelations ConstructiveTypeCopyHeapMatch
open ConstructiveTypeCopyRealization
open ConstructiveTypeCopy ConstructiveTypeCopySemantics ConstructiveTypeEnvironment

section Lift
variable {H K : heaptype → heaptype → Prop} (hk : ∀ a b, H a b → K a b)
include hk

theorem ref_imp {a b : reftype} (h : RefRel H a b) : RefRel K a b := by
  cases h with | mk nu a b h => exact .mk nu a b (hk a b h)

theorem val_imp {a b : valtype} (h : ValRel H a b) : ValRel K a b := by
  cases h with
  | num n => exact .num n
  | vec v => exact .vec v
  | bot => exact .bot
  | ref a b h => exact .ref a b (ref_imp hk h)

theorem storage_imp {a b : storagetype} (h : StorageRel H a b) : StorageRel K a b := by
  cases h with
  | val a b h => exact .val a b (val_imp hk h)
  | pack p => exact .pack p

theorem field_imp {a b : fieldtype} (h : FieldRel H a b) : FieldRel K a b := by
  cases h with | mk mu a b h => exact .mk mu a b (storage_imp hk h)

theorem str_imp {a b : strtype} (h : StrRel H a b) : StrRel K a b := by
  cases h with
  | struct as bs h => exact .struct as bs (h.imp (fun _ _ h => field_imp hk h))
  | array a b h => exact .array a b (field_imp hk h)
  | func ai bi ao bo hi ho =>
    exact .func ai bi ao bo (hi.imp (fun _ _ h => val_imp hk h)) (ho.imp (fun _ _ h => val_imp hk h))
end Lift

/-- A raw signature has the same denotation as the actual closed definition at
its position. This invariant contains evidence only, never a runtime check. -/
def At (full : context) (i : Nat) (fin : final) (raw : strtype) : Prop :=
  ∃ dt ps closed, full.TYPES[i]? = some dt ∧
    unrollDeftypeResult dt = some (.SubT fin ps closed) ∧
    StrRel (HeapRel full full) raw closed

def Describes (c full : context) (env : List (Signature c)) : Prop :=
  ∀ i s, env[i]? = some s → At full i s.header.finality s.shape

def Remaining (full : context) (base : Nat) (sts : List SpecTec.subtype) : Prop :=
  ∀ i fin ps st, sts[i]? = some (.SubT fin ps st) → At full (base+i) fin st

theorem at_prefix (c d : context) (tail : List deftype)
    (he : d.TYPES = c.TYPES ++ tail) (i : Nat) (fin : final) (st : strtype)
    (h : At c i fin st) : At d i fin st := by
  obtain ⟨dt,ps,closed,hget,hu,hr⟩ := h
  refine ⟨dt,ps,closed,?_,hu,str_imp ?_ hr⟩
  · rw [he,List.getElem?_append_left (List.getElem?_eq_some_iff.mp hget).1]
    exact hget
  · rintro a b ⟨v,ha,hb⟩
    exact ⟨v,ConstructiveTypeCopyPrefix.resolves_prefix c d tail he a v ha,
      ConstructiveTypeCopyPrefix.resolves_prefix c d tail he b v hb⟩

theorem describes_lift (c d : context) (tail : List deftype)
    (he : d.TYPES = c.TYPES ++ tail) (env : List (Signature c))
    (h : Describes c c env) (n : Nat) :
    Describes (ConstructiveFreshSignatures.capacity c n) d
      (ConstructiveFreshSignatures.liftEnv c n env) := by
  intro i s hs
  simp only [ConstructiveFreshSignatures.liftEnv,List.getElem?_map] at hs
  obtain ⟨s',hget,rfl⟩ := Option.map_eq_some_iff.mp hs
  exact at_prefix c d tail he i s'.header.finality s'.shape (h i s' hget)

theorem describes_append (c full : context) (env : List (Signature c)) (s : Signature c)
    (h : Describes c full env) (hs : At full env.length s.header.finality s.shape) :
    Describes c full (env ++ [s]) := by
  intro i t ht
  by_cases hi : i < env.length
  · exact h i t (by simpa [List.getElem?_append_left hi] using ht)
  · have hle : env.length ≤ i := by omega
    rw [List.getElem?_append_right hle] at ht
    have hi0 : i-env.length = 0 := by
      have hb := (List.getElem?_eq_some_iff.mp ht).1
      simp only [List.length_singleton] at hb
      omega
    have heq : s = t := by simpa [hi0] using ht
    have hipos : i = env.length := by omega
    simpa [hipos,← heq] using hs

theorem remaining_tail (full : context) (base : Nat) (st : SpecTec.subtype)
    (sts : List SpecTec.subtype) (h : Remaining full base (st::sts)) :
    Remaining full (base+1) sts := by
  intro i f ps s hg
  simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
    h (i+1) f ps s (by simpa using hg)

theorem remaining_closed (c : context) (sts : List SpecTec.subtype)
    (h : GroupBound (c.TYPES.length+sts.length) sts) :
    Remaining (extended c sts h) c.TYPES.length sts := by
  intro i f ps st hg
  have hs := h _ (List.mem_of_getElem? hg)
  let rt := groupValue c.TYPES c.TYPES.length (Nat.le_refl _) sts h
  refine ⟨.DefT rt i,
    unrollHeaptypes (mapP _ (heapValue c.TYPES c.TYPES.length sts.length (Nat.le_refl _)) ps hs.1) rt,
    unrollStrtype (strValue c.TYPES c.TYPES.length sts.length (Nat.le_refl _) st hs.2) rt,
    definition_lookup c.TYPES rt sts.length i (List.getElem?_eq_some_iff.mp hg).1,?_,?_⟩
  · exact group_unroll c.TYPES sts h i f ps st hg hs
  · exact ConstructiveTypeSignatures.str_closed c sts h st hs.2

end properties.wasm_module_ok.ConstructiveSignatureState
