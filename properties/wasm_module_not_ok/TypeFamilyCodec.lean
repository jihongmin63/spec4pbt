import properties.wasm_module_not_ok.ModuleEncoding

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace properties.wasm_module_not_ok.TypeFamilyCodec

mutual

def depthHeaptype : SpecTec.heaptype → Nat
  | .AnyHT => 1
  | .NoneHT => 1
  | .EqHT => 1
  | .I31HT => 1
  | .StructHT => 1
  | .ArrayHT => 1
  | .FuncHT => 1
  | .NoFuncHT => 1
  | .ExnHT => 1
  | .NoExnHT => 1
  | .ExternHT => 1
  | .NoExternHT => 1
  | .VarHT x0 => 1
  | .DefHT x0 => depthDeftype x0 + 1
  | .BotHT => 1

def depthReftype : SpecTec.reftype → Nat
  | .«% %» x0 x1 => depthHeaptype x1 + 1

def depthValtype : SpecTec.valtype → Nat
  | .NumT x0 => 1
  | .VecT x0 => 1
  | .RefT x0 => depthReftype x0 + 1
  | .BotT => 1

def depthStoragetype : SpecTec.storagetype → Nat
  | .ValStorageT x0 => depthValtype x0 + 1
  | .PackStorageT x0 => 1

def depthFieldtype : SpecTec.fieldtype → Nat
  | .FieldT x0 x1 => depthStoragetype x1 + 1

def depthStructtype : SpecTec.structtype → Nat
  | .StructT x0 => depthListFieldtype x0 + 1

def depthArraytype : SpecTec.arraytype → Nat
  | .ArrayT x0 => depthFieldtype x0 + 1

def depthFunctype : SpecTec.functype → Nat
  | .FuncT x0 x1 => max (depthListValtype x0) (depthListValtype x1) + 1

def depthStrtype : SpecTec.strtype → Nat
  | .DefStructT x0 => depthStructtype x0 + 1
  | .DefArrayT x0 => depthArraytype x0 + 1
  | .DefFuncT x0 => depthFunctype x0 + 1

def depthSubtype : SpecTec.subtype → Nat
  | .SubT x0 x1 x2 => max (depthListHeaptype x1) (depthStrtype x2) + 1

def depthRectype : SpecTec.rectype → Nat
  | .RecT x0 => depthListSubtype x0 + 1

def depthDeftype : SpecTec.deftype → Nat
  | .DefT x0 x1 => depthRectype x0 + 1

def depthListFieldtype : List SpecTec.fieldtype → Nat
  | [] => 0
  | x :: xs => max (depthFieldtype x) (depthListFieldtype xs) + 1

def depthListValtype : List SpecTec.valtype → Nat
  | [] => 0
  | x :: xs => max (depthValtype x) (depthListValtype xs) + 1

def depthListHeaptype : List SpecTec.heaptype → Nat
  | [] => 0
  | x :: xs => max (depthHeaptype x) (depthListHeaptype xs) + 1

def depthListSubtype : List SpecTec.subtype → Nat
  | [] => 0
  | x :: xs => max (depthSubtype x) (depthListSubtype xs) + 1

end

mutual

def encodeHeaptype : SpecTec.heaptype → Nat
  | .AnyHT => Nat.pair 0 (0) + 1
  | .NoneHT => Nat.pair 1 (0) + 1
  | .EqHT => Nat.pair 2 (0) + 1
  | .I31HT => Nat.pair 3 (0) + 1
  | .StructHT => Nat.pair 4 (0) + 1
  | .ArrayHT => Nat.pair 5 (0) + 1
  | .FuncHT => Nat.pair 6 (0) + 1
  | .NoFuncHT => Nat.pair 7 (0) + 1
  | .ExnHT => Nat.pair 8 (0) + 1
  | .NoExnHT => Nat.pair 9 (0) + 1
  | .ExternHT => Nat.pair 10 (0) + 1
  | .NoExternHT => Nat.pair 11 (0) + 1
  | .VarHT x0 => Nat.pair 12 (Encodable.encode x0) + 1
  | .DefHT x0 => Nat.pair 13 (encodeDeftype x0) + 1
  | .BotHT => Nat.pair 14 (0) + 1

def encodeReftype : SpecTec.reftype → Nat
  | .«% %» x0 x1 => Nat.pair 0 (Nat.pair (Encodable.encode x0) (encodeHeaptype x1)) + 1

def encodeValtype : SpecTec.valtype → Nat
  | .NumT x0 => Nat.pair 0 (Encodable.encode x0) + 1
  | .VecT x0 => Nat.pair 1 (Encodable.encode x0) + 1
  | .RefT x0 => Nat.pair 2 (encodeReftype x0) + 1
  | .BotT => Nat.pair 3 (0) + 1

def encodeStoragetype : SpecTec.storagetype → Nat
  | .ValStorageT x0 => Nat.pair 0 (encodeValtype x0) + 1
  | .PackStorageT x0 => Nat.pair 1 (Encodable.encode x0) + 1

def encodeFieldtype : SpecTec.fieldtype → Nat
  | .FieldT x0 x1 => Nat.pair 0 (Nat.pair (Encodable.encode x0) (encodeStoragetype x1)) + 1

def encodeStructtype : SpecTec.structtype → Nat
  | .StructT x0 => Nat.pair 0 (encodeListFieldtype x0) + 1

def encodeArraytype : SpecTec.arraytype → Nat
  | .ArrayT x0 => Nat.pair 0 (encodeFieldtype x0) + 1

def encodeFunctype : SpecTec.functype → Nat
  | .FuncT x0 x1 => Nat.pair 0 (Nat.pair (encodeListValtype x0) (encodeListValtype x1)) + 1

def encodeStrtype : SpecTec.strtype → Nat
  | .DefStructT x0 => Nat.pair 0 (encodeStructtype x0) + 1
  | .DefArrayT x0 => Nat.pair 1 (encodeArraytype x0) + 1
  | .DefFuncT x0 => Nat.pair 2 (encodeFunctype x0) + 1

def encodeSubtype : SpecTec.subtype → Nat
  | .SubT x0 x1 x2 => Nat.pair 0 (Nat.pair (Encodable.encode x0) (Nat.pair (encodeListHeaptype x1) (encodeStrtype x2))) + 1

def encodeRectype : SpecTec.rectype → Nat
  | .RecT x0 => Nat.pair 0 (encodeListSubtype x0) + 1

def encodeDeftype : SpecTec.deftype → Nat
  | .DefT x0 x1 => Nat.pair 0 (Nat.pair (encodeRectype x0) (Encodable.encode x1)) + 1

def encodeListFieldtype : List SpecTec.fieldtype → Nat
  | [] => 0
  | x :: xs => Nat.pair (encodeFieldtype x) (encodeListFieldtype xs) + 1

def encodeListValtype : List SpecTec.valtype → Nat
  | [] => 0
  | x :: xs => Nat.pair (encodeValtype x) (encodeListValtype xs) + 1

def encodeListHeaptype : List SpecTec.heaptype → Nat
  | [] => 0
  | x :: xs => Nat.pair (encodeHeaptype x) (encodeListHeaptype xs) + 1

def encodeListSubtype : List SpecTec.subtype → Nat
  | [] => 0
  | x :: xs => Nat.pair (encodeSubtype x) (encodeListSubtype xs) + 1

end

mutual

def decodeHeaptypeFuel : Nat → Nat → Option (SpecTec.heaptype)
  | 0, _ => none
  | _ + 1, 0 => none
  | fuel + 1, code + 1 =>
      let p := Nat.unpair code
      match p.1 with
      | 0 =>
          some SpecTec.heaptype.AnyHT
      | 1 =>
          some SpecTec.heaptype.NoneHT
      | 2 =>
          some SpecTec.heaptype.EqHT
      | 3 =>
          some SpecTec.heaptype.I31HT
      | 4 =>
          some SpecTec.heaptype.StructHT
      | 5 =>
          some SpecTec.heaptype.ArrayHT
      | 6 =>
          some SpecTec.heaptype.FuncHT
      | 7 =>
          some SpecTec.heaptype.NoFuncHT
      | 8 =>
          some SpecTec.heaptype.ExnHT
      | 9 =>
          some SpecTec.heaptype.NoExnHT
      | 10 =>
          some SpecTec.heaptype.ExternHT
      | 11 =>
          some SpecTec.heaptype.NoExternHT
      | 12 =>
          SpecTec.heaptype.VarHT <$> Encodable.decode p.2
      | 13 =>
          SpecTec.heaptype.DefHT <$> decodeDeftypeFuel fuel p.2
      | 14 =>
          some SpecTec.heaptype.BotHT
      | _ => none

def decodeReftypeFuel : Nat → Nat → Option (SpecTec.reftype)
  | 0, _ => none
  | _ + 1, 0 => none
  | fuel + 1, code + 1 =>
      let p := Nat.unpair code
      match p.1 with
      | 0 =>
          let q0 := Nat.unpair p.2
          SpecTec.reftype.«% %» <$> Encodable.decode q0.1 <*> decodeHeaptypeFuel fuel q0.2
      | _ => none

def decodeValtypeFuel : Nat → Nat → Option (SpecTec.valtype)
  | 0, _ => none
  | _ + 1, 0 => none
  | fuel + 1, code + 1 =>
      let p := Nat.unpair code
      match p.1 with
      | 0 =>
          SpecTec.valtype.NumT <$> Encodable.decode p.2
      | 1 =>
          SpecTec.valtype.VecT <$> Encodable.decode p.2
      | 2 =>
          SpecTec.valtype.RefT <$> decodeReftypeFuel fuel p.2
      | 3 =>
          some SpecTec.valtype.BotT
      | _ => none

def decodeStoragetypeFuel : Nat → Nat → Option (SpecTec.storagetype)
  | 0, _ => none
  | _ + 1, 0 => none
  | fuel + 1, code + 1 =>
      let p := Nat.unpair code
      match p.1 with
      | 0 =>
          SpecTec.storagetype.ValStorageT <$> decodeValtypeFuel fuel p.2
      | 1 =>
          SpecTec.storagetype.PackStorageT <$> Encodable.decode p.2
      | _ => none

def decodeFieldtypeFuel : Nat → Nat → Option (SpecTec.fieldtype)
  | 0, _ => none
  | _ + 1, 0 => none
  | fuel + 1, code + 1 =>
      let p := Nat.unpair code
      match p.1 with
      | 0 =>
          let q0 := Nat.unpair p.2
          SpecTec.fieldtype.FieldT <$> Encodable.decode q0.1 <*> decodeStoragetypeFuel fuel q0.2
      | _ => none

def decodeStructtypeFuel : Nat → Nat → Option (SpecTec.structtype)
  | 0, _ => none
  | _ + 1, 0 => none
  | fuel + 1, code + 1 =>
      let p := Nat.unpair code
      match p.1 with
      | 0 =>
          SpecTec.structtype.StructT <$> decodeListFieldtypeFuel fuel p.2
      | _ => none

def decodeArraytypeFuel : Nat → Nat → Option (SpecTec.arraytype)
  | 0, _ => none
  | _ + 1, 0 => none
  | fuel + 1, code + 1 =>
      let p := Nat.unpair code
      match p.1 with
      | 0 =>
          SpecTec.arraytype.ArrayT <$> decodeFieldtypeFuel fuel p.2
      | _ => none

def decodeFunctypeFuel : Nat → Nat → Option (SpecTec.functype)
  | 0, _ => none
  | _ + 1, 0 => none
  | fuel + 1, code + 1 =>
      let p := Nat.unpair code
      match p.1 with
      | 0 =>
          let q0 := Nat.unpair p.2
          SpecTec.functype.FuncT <$> decodeListValtypeFuel fuel q0.1 <*> decodeListValtypeFuel fuel q0.2
      | _ => none

def decodeStrtypeFuel : Nat → Nat → Option (SpecTec.strtype)
  | 0, _ => none
  | _ + 1, 0 => none
  | fuel + 1, code + 1 =>
      let p := Nat.unpair code
      match p.1 with
      | 0 =>
          SpecTec.strtype.DefStructT <$> decodeStructtypeFuel fuel p.2
      | 1 =>
          SpecTec.strtype.DefArrayT <$> decodeArraytypeFuel fuel p.2
      | 2 =>
          SpecTec.strtype.DefFuncT <$> decodeFunctypeFuel fuel p.2
      | _ => none

def decodeSubtypeFuel : Nat → Nat → Option (SpecTec.subtype)
  | 0, _ => none
  | _ + 1, 0 => none
  | fuel + 1, code + 1 =>
      let p := Nat.unpair code
      match p.1 with
      | 0 =>
          let q0 := Nat.unpair p.2
          let q1 := Nat.unpair q0.2
          SpecTec.subtype.SubT <$> Encodable.decode q0.1 <*> decodeListHeaptypeFuel fuel q1.1 <*> decodeStrtypeFuel fuel q1.2
      | _ => none

def decodeRectypeFuel : Nat → Nat → Option (SpecTec.rectype)
  | 0, _ => none
  | _ + 1, 0 => none
  | fuel + 1, code + 1 =>
      let p := Nat.unpair code
      match p.1 with
      | 0 =>
          SpecTec.rectype.RecT <$> decodeListSubtypeFuel fuel p.2
      | _ => none

def decodeDeftypeFuel : Nat → Nat → Option (SpecTec.deftype)
  | 0, _ => none
  | _ + 1, 0 => none
  | fuel + 1, code + 1 =>
      let p := Nat.unpair code
      match p.1 with
      | 0 =>
          let q0 := Nat.unpair p.2
          SpecTec.deftype.DefT <$> decodeRectypeFuel fuel q0.1 <*> Encodable.decode q0.2
      | _ => none

def decodeListFieldtypeFuel : Nat → Nat → Option (List SpecTec.fieldtype)
  | 0, _ => none
  | _ + 1, 0 => some []
  | fuel + 1, code + 1 =>
      let p := Nat.unpair code
      List.cons <$> decodeFieldtypeFuel fuel p.1 <*> decodeListFieldtypeFuel fuel p.2

def decodeListValtypeFuel : Nat → Nat → Option (List SpecTec.valtype)
  | 0, _ => none
  | _ + 1, 0 => some []
  | fuel + 1, code + 1 =>
      let p := Nat.unpair code
      List.cons <$> decodeValtypeFuel fuel p.1 <*> decodeListValtypeFuel fuel p.2

def decodeListHeaptypeFuel : Nat → Nat → Option (List SpecTec.heaptype)
  | 0, _ => none
  | _ + 1, 0 => some []
  | fuel + 1, code + 1 =>
      let p := Nat.unpair code
      List.cons <$> decodeHeaptypeFuel fuel p.1 <*> decodeListHeaptypeFuel fuel p.2

def decodeListSubtypeFuel : Nat → Nat → Option (List SpecTec.subtype)
  | 0, _ => none
  | _ + 1, 0 => some []
  | fuel + 1, code + 1 =>
      let p := Nat.unpair code
      List.cons <$> decodeSubtypeFuel fuel p.1 <*> decodeListSubtypeFuel fuel p.2

end

structure FuelRoundtrip (fuel : Nat) : Prop where
  heaptype : ∀ x : SpecTec.heaptype, depthHeaptype x < fuel →
    decodeHeaptypeFuel fuel (encodeHeaptype x) = some x
  reftype : ∀ x : SpecTec.reftype, depthReftype x < fuel →
    decodeReftypeFuel fuel (encodeReftype x) = some x
  valtype : ∀ x : SpecTec.valtype, depthValtype x < fuel →
    decodeValtypeFuel fuel (encodeValtype x) = some x
  storagetype : ∀ x : SpecTec.storagetype, depthStoragetype x < fuel →
    decodeStoragetypeFuel fuel (encodeStoragetype x) = some x
  fieldtype : ∀ x : SpecTec.fieldtype, depthFieldtype x < fuel →
    decodeFieldtypeFuel fuel (encodeFieldtype x) = some x
  structtype : ∀ x : SpecTec.structtype, depthStructtype x < fuel →
    decodeStructtypeFuel fuel (encodeStructtype x) = some x
  arraytype : ∀ x : SpecTec.arraytype, depthArraytype x < fuel →
    decodeArraytypeFuel fuel (encodeArraytype x) = some x
  functype : ∀ x : SpecTec.functype, depthFunctype x < fuel →
    decodeFunctypeFuel fuel (encodeFunctype x) = some x
  strtype : ∀ x : SpecTec.strtype, depthStrtype x < fuel →
    decodeStrtypeFuel fuel (encodeStrtype x) = some x
  subtype : ∀ x : SpecTec.subtype, depthSubtype x < fuel →
    decodeSubtypeFuel fuel (encodeSubtype x) = some x
  rectype : ∀ x : SpecTec.rectype, depthRectype x < fuel →
    decodeRectypeFuel fuel (encodeRectype x) = some x
  deftype : ∀ x : SpecTec.deftype, depthDeftype x < fuel →
    decodeDeftypeFuel fuel (encodeDeftype x) = some x
  list_fieldtype : ∀ x : List SpecTec.fieldtype, depthListFieldtype x < fuel →
    decodeListFieldtypeFuel fuel (encodeListFieldtype x) = some x
  list_valtype : ∀ x : List SpecTec.valtype, depthListValtype x < fuel →
    decodeListValtypeFuel fuel (encodeListValtype x) = some x
  list_heaptype : ∀ x : List SpecTec.heaptype, depthListHeaptype x < fuel →
    decodeListHeaptypeFuel fuel (encodeListHeaptype x) = some x
  list_subtype : ∀ x : List SpecTec.subtype, depthListSubtype x < fuel →
    decodeListSubtypeFuel fuel (encodeListSubtype x) = some x

theorem fuelRoundtrip (fuel : Nat) : FuelRoundtrip fuel := by
  induction fuel with
  | zero =>
    constructor <;> intro x h <;> omega
  | succ fuel ih =>
    constructor
    · intro x h
      cases x with
      | AnyHT =>
        simp [encodeHeaptype, decodeHeaptypeFuel, Nat.unpair_pair, Encodable.encodek]
      | NoneHT =>
        simp [encodeHeaptype, decodeHeaptypeFuel, Nat.unpair_pair, Encodable.encodek]
      | EqHT =>
        simp [encodeHeaptype, decodeHeaptypeFuel, Nat.unpair_pair, Encodable.encodek]
      | I31HT =>
        simp [encodeHeaptype, decodeHeaptypeFuel, Nat.unpair_pair, Encodable.encodek]
      | StructHT =>
        simp [encodeHeaptype, decodeHeaptypeFuel, Nat.unpair_pair, Encodable.encodek]
      | ArrayHT =>
        simp [encodeHeaptype, decodeHeaptypeFuel, Nat.unpair_pair, Encodable.encodek]
      | FuncHT =>
        simp [encodeHeaptype, decodeHeaptypeFuel, Nat.unpair_pair, Encodable.encodek]
      | NoFuncHT =>
        simp [encodeHeaptype, decodeHeaptypeFuel, Nat.unpair_pair, Encodable.encodek]
      | ExnHT =>
        simp [encodeHeaptype, decodeHeaptypeFuel, Nat.unpair_pair, Encodable.encodek]
      | NoExnHT =>
        simp [encodeHeaptype, decodeHeaptypeFuel, Nat.unpair_pair, Encodable.encodek]
      | ExternHT =>
        simp [encodeHeaptype, decodeHeaptypeFuel, Nat.unpair_pair, Encodable.encodek]
      | NoExternHT =>
        simp [encodeHeaptype, decodeHeaptypeFuel, Nat.unpair_pair, Encodable.encodek]
      | VarHT x0 =>
        simp [encodeHeaptype, decodeHeaptypeFuel, Nat.unpair_pair, Encodable.encodek]
      | DefHT x0 =>
        have h0 : depthDeftype x0 < fuel := by
          simp [depthHeaptype] at h
          omega
        simp [encodeHeaptype, decodeHeaptypeFuel, Nat.unpair_pair, Encodable.encodek, ih.deftype x0 h0]
      | BotHT =>
        simp [encodeHeaptype, decodeHeaptypeFuel, Nat.unpair_pair, Encodable.encodek]
    · intro x h
      cases x with
      | «% %» x0 x1 =>
        have h1 : depthHeaptype x1 < fuel := by
          simp [depthReftype] at h
          omega
        simp [encodeReftype, decodeReftypeFuel, Nat.unpair_pair, Encodable.encodek, ih.heaptype x1 h1]
    · intro x h
      cases x with
      | NumT x0 =>
        simp [encodeValtype, decodeValtypeFuel, Nat.unpair_pair, Encodable.encodek]
      | VecT x0 =>
        simp [encodeValtype, decodeValtypeFuel, Nat.unpair_pair, Encodable.encodek]
      | RefT x0 =>
        have h0 : depthReftype x0 < fuel := by
          simp [depthValtype] at h
          omega
        simp [encodeValtype, decodeValtypeFuel, Nat.unpair_pair, Encodable.encodek, ih.reftype x0 h0]
      | BotT =>
        simp [encodeValtype, decodeValtypeFuel, Nat.unpair_pair, Encodable.encodek]
    · intro x h
      cases x with
      | ValStorageT x0 =>
        have h0 : depthValtype x0 < fuel := by
          simp [depthStoragetype] at h
          omega
        simp [encodeStoragetype, decodeStoragetypeFuel, Nat.unpair_pair, Encodable.encodek, ih.valtype x0 h0]
      | PackStorageT x0 =>
        simp [encodeStoragetype, decodeStoragetypeFuel, Nat.unpair_pair, Encodable.encodek]
    · intro x h
      cases x with
      | FieldT x0 x1 =>
        have h1 : depthStoragetype x1 < fuel := by
          simp [depthFieldtype] at h
          omega
        simp [encodeFieldtype, decodeFieldtypeFuel, Nat.unpair_pair, Encodable.encodek, ih.storagetype x1 h1]
    · intro x h
      cases x with
      | StructT x0 =>
        have h0 : depthListFieldtype x0 < fuel := by
          simp [depthStructtype] at h
          omega
        simp [encodeStructtype, decodeStructtypeFuel, Nat.unpair_pair, Encodable.encodek, ih.list_fieldtype x0 h0]
    · intro x h
      cases x with
      | ArrayT x0 =>
        have h0 : depthFieldtype x0 < fuel := by
          simp [depthArraytype] at h
          omega
        simp [encodeArraytype, decodeArraytypeFuel, Nat.unpair_pair, Encodable.encodek, ih.fieldtype x0 h0]
    · intro x h
      cases x with
      | FuncT x0 x1 =>
        have h0 : depthListValtype x0 < fuel := by
          simp [depthFunctype] at h
          omega
        have h1 : depthListValtype x1 < fuel := by
          simp [depthFunctype] at h
          omega
        simp [encodeFunctype, decodeFunctypeFuel, Nat.unpair_pair, Encodable.encodek, ih.list_valtype x0 h0, ih.list_valtype x1 h1]
    · intro x h
      cases x with
      | DefStructT x0 =>
        have h0 : depthStructtype x0 < fuel := by
          simp [depthStrtype] at h
          omega
        simp [encodeStrtype, decodeStrtypeFuel, Nat.unpair_pair, Encodable.encodek, ih.structtype x0 h0]
      | DefArrayT x0 =>
        have h0 : depthArraytype x0 < fuel := by
          simp [depthStrtype] at h
          omega
        simp [encodeStrtype, decodeStrtypeFuel, Nat.unpair_pair, Encodable.encodek, ih.arraytype x0 h0]
      | DefFuncT x0 =>
        have h0 : depthFunctype x0 < fuel := by
          simp [depthStrtype] at h
          omega
        simp [encodeStrtype, decodeStrtypeFuel, Nat.unpair_pair, Encodable.encodek, ih.functype x0 h0]
    · intro x h
      cases x with
      | SubT x0 x1 x2 =>
        have h1 : depthListHeaptype x1 < fuel := by
          simp [depthSubtype] at h
          omega
        have h2 : depthStrtype x2 < fuel := by
          simp [depthSubtype] at h
          omega
        simp [encodeSubtype, decodeSubtypeFuel, Nat.unpair_pair, Encodable.encodek, ih.list_heaptype x1 h1, ih.strtype x2 h2]
    · intro x h
      cases x with
      | RecT x0 =>
        have h0 : depthListSubtype x0 < fuel := by
          simp [depthRectype] at h
          omega
        simp [encodeRectype, decodeRectypeFuel, Nat.unpair_pair, Encodable.encodek, ih.list_subtype x0 h0]
    · intro x h
      cases x with
      | DefT x0 x1 =>
        have h0 : depthRectype x0 < fuel := by
          simp [depthDeftype] at h
          omega
        simp [encodeDeftype, decodeDeftypeFuel, Nat.unpair_pair, Encodable.encodek, ih.rectype x0 h0]
    · intro x h
      cases x with
      | nil => simp [encodeListFieldtype, decodeListFieldtypeFuel]
      | cons a as =>
        have ha : depthFieldtype a < fuel := by
          simp [depthListFieldtype] at h
          omega
        have has : depthListFieldtype as < fuel := by
          simp [depthListFieldtype] at h
          omega
        simp [encodeListFieldtype, decodeListFieldtypeFuel, Nat.unpair_pair,
          ih.fieldtype a ha, ih.list_fieldtype as has]
    · intro x h
      cases x with
      | nil => simp [encodeListValtype, decodeListValtypeFuel]
      | cons a as =>
        have ha : depthValtype a < fuel := by
          simp [depthListValtype] at h
          omega
        have has : depthListValtype as < fuel := by
          simp [depthListValtype] at h
          omega
        simp [encodeListValtype, decodeListValtypeFuel, Nat.unpair_pair,
          ih.valtype a ha, ih.list_valtype as has]
    · intro x h
      cases x with
      | nil => simp [encodeListHeaptype, decodeListHeaptypeFuel]
      | cons a as =>
        have ha : depthHeaptype a < fuel := by
          simp [depthListHeaptype] at h
          omega
        have has : depthListHeaptype as < fuel := by
          simp [depthListHeaptype] at h
          omega
        simp [encodeListHeaptype, decodeListHeaptypeFuel, Nat.unpair_pair,
          ih.heaptype a ha, ih.list_heaptype as has]
    · intro x h
      cases x with
      | nil => simp [encodeListSubtype, decodeListSubtypeFuel]
      | cons a as =>
        have ha : depthSubtype a < fuel := by
          simp [depthListSubtype] at h
          omega
        have has : depthListSubtype as < fuel := by
          simp [depthListSubtype] at h
          omega
        simp [encodeListSubtype, decodeListSubtypeFuel, Nat.unpair_pair,
          ih.subtype a ha, ih.list_subtype as has]


def fullEncodeHeaptype (x : SpecTec.heaptype) : Nat :=
  Nat.pair (depthHeaptype x + 1) (encodeHeaptype x)

def fullDecodeHeaptype (n : Nat) : Option SpecTec.heaptype :=
  let p := Nat.unpair n
  decodeHeaptypeFuel p.1 p.2

theorem fullHeaptype_roundtrip (x : SpecTec.heaptype) :
    fullDecodeHeaptype (fullEncodeHeaptype x) = some x := by
  simpa [fullDecodeHeaptype, fullEncodeHeaptype, Nat.unpair_pair] using
    (fuelRoundtrip (depthHeaptype x + 1)).heaptype x (Nat.lt_succ_self _)

instance : Encodable SpecTec.heaptype :=
  Encodable.ofLeftInjection fullEncodeHeaptype fullDecodeHeaptype fullHeaptype_roundtrip

def fullEncodeReftype (x : SpecTec.reftype) : Nat :=
  Nat.pair (depthReftype x + 1) (encodeReftype x)

def fullDecodeReftype (n : Nat) : Option SpecTec.reftype :=
  let p := Nat.unpair n
  decodeReftypeFuel p.1 p.2

theorem fullReftype_roundtrip (x : SpecTec.reftype) :
    fullDecodeReftype (fullEncodeReftype x) = some x := by
  simpa [fullDecodeReftype, fullEncodeReftype, Nat.unpair_pair] using
    (fuelRoundtrip (depthReftype x + 1)).reftype x (Nat.lt_succ_self _)

instance : Encodable SpecTec.reftype :=
  Encodable.ofLeftInjection fullEncodeReftype fullDecodeReftype fullReftype_roundtrip

def fullEncodeValtype (x : SpecTec.valtype) : Nat :=
  Nat.pair (depthValtype x + 1) (encodeValtype x)

def fullDecodeValtype (n : Nat) : Option SpecTec.valtype :=
  let p := Nat.unpair n
  decodeValtypeFuel p.1 p.2

theorem fullValtype_roundtrip (x : SpecTec.valtype) :
    fullDecodeValtype (fullEncodeValtype x) = some x := by
  simpa [fullDecodeValtype, fullEncodeValtype, Nat.unpair_pair] using
    (fuelRoundtrip (depthValtype x + 1)).valtype x (Nat.lt_succ_self _)

instance : Encodable SpecTec.valtype :=
  Encodable.ofLeftInjection fullEncodeValtype fullDecodeValtype fullValtype_roundtrip

def fullEncodeStoragetype (x : SpecTec.storagetype) : Nat :=
  Nat.pair (depthStoragetype x + 1) (encodeStoragetype x)

def fullDecodeStoragetype (n : Nat) : Option SpecTec.storagetype :=
  let p := Nat.unpair n
  decodeStoragetypeFuel p.1 p.2

theorem fullStoragetype_roundtrip (x : SpecTec.storagetype) :
    fullDecodeStoragetype (fullEncodeStoragetype x) = some x := by
  simpa [fullDecodeStoragetype, fullEncodeStoragetype, Nat.unpair_pair] using
    (fuelRoundtrip (depthStoragetype x + 1)).storagetype x (Nat.lt_succ_self _)

instance : Encodable SpecTec.storagetype :=
  Encodable.ofLeftInjection fullEncodeStoragetype fullDecodeStoragetype fullStoragetype_roundtrip

def fullEncodeFieldtype (x : SpecTec.fieldtype) : Nat :=
  Nat.pair (depthFieldtype x + 1) (encodeFieldtype x)

def fullDecodeFieldtype (n : Nat) : Option SpecTec.fieldtype :=
  let p := Nat.unpair n
  decodeFieldtypeFuel p.1 p.2

theorem fullFieldtype_roundtrip (x : SpecTec.fieldtype) :
    fullDecodeFieldtype (fullEncodeFieldtype x) = some x := by
  simpa [fullDecodeFieldtype, fullEncodeFieldtype, Nat.unpair_pair] using
    (fuelRoundtrip (depthFieldtype x + 1)).fieldtype x (Nat.lt_succ_self _)

instance : Encodable SpecTec.fieldtype :=
  Encodable.ofLeftInjection fullEncodeFieldtype fullDecodeFieldtype fullFieldtype_roundtrip

def fullEncodeStructtype (x : SpecTec.structtype) : Nat :=
  Nat.pair (depthStructtype x + 1) (encodeStructtype x)

def fullDecodeStructtype (n : Nat) : Option SpecTec.structtype :=
  let p := Nat.unpair n
  decodeStructtypeFuel p.1 p.2

theorem fullStructtype_roundtrip (x : SpecTec.structtype) :
    fullDecodeStructtype (fullEncodeStructtype x) = some x := by
  simpa [fullDecodeStructtype, fullEncodeStructtype, Nat.unpair_pair] using
    (fuelRoundtrip (depthStructtype x + 1)).structtype x (Nat.lt_succ_self _)

instance : Encodable SpecTec.structtype :=
  Encodable.ofLeftInjection fullEncodeStructtype fullDecodeStructtype fullStructtype_roundtrip

def fullEncodeArraytype (x : SpecTec.arraytype) : Nat :=
  Nat.pair (depthArraytype x + 1) (encodeArraytype x)

def fullDecodeArraytype (n : Nat) : Option SpecTec.arraytype :=
  let p := Nat.unpair n
  decodeArraytypeFuel p.1 p.2

theorem fullArraytype_roundtrip (x : SpecTec.arraytype) :
    fullDecodeArraytype (fullEncodeArraytype x) = some x := by
  simpa [fullDecodeArraytype, fullEncodeArraytype, Nat.unpair_pair] using
    (fuelRoundtrip (depthArraytype x + 1)).arraytype x (Nat.lt_succ_self _)

instance : Encodable SpecTec.arraytype :=
  Encodable.ofLeftInjection fullEncodeArraytype fullDecodeArraytype fullArraytype_roundtrip

def fullEncodeFunctype (x : SpecTec.functype) : Nat :=
  Nat.pair (depthFunctype x + 1) (encodeFunctype x)

def fullDecodeFunctype (n : Nat) : Option SpecTec.functype :=
  let p := Nat.unpair n
  decodeFunctypeFuel p.1 p.2

theorem fullFunctype_roundtrip (x : SpecTec.functype) :
    fullDecodeFunctype (fullEncodeFunctype x) = some x := by
  simpa [fullDecodeFunctype, fullEncodeFunctype, Nat.unpair_pair] using
    (fuelRoundtrip (depthFunctype x + 1)).functype x (Nat.lt_succ_self _)

instance : Encodable SpecTec.functype :=
  Encodable.ofLeftInjection fullEncodeFunctype fullDecodeFunctype fullFunctype_roundtrip

def fullEncodeStrtype (x : SpecTec.strtype) : Nat :=
  Nat.pair (depthStrtype x + 1) (encodeStrtype x)

def fullDecodeStrtype (n : Nat) : Option SpecTec.strtype :=
  let p := Nat.unpair n
  decodeStrtypeFuel p.1 p.2

theorem fullStrtype_roundtrip (x : SpecTec.strtype) :
    fullDecodeStrtype (fullEncodeStrtype x) = some x := by
  simpa [fullDecodeStrtype, fullEncodeStrtype, Nat.unpair_pair] using
    (fuelRoundtrip (depthStrtype x + 1)).strtype x (Nat.lt_succ_self _)

instance : Encodable SpecTec.strtype :=
  Encodable.ofLeftInjection fullEncodeStrtype fullDecodeStrtype fullStrtype_roundtrip

def fullEncodeSubtype (x : SpecTec.subtype) : Nat :=
  Nat.pair (depthSubtype x + 1) (encodeSubtype x)

def fullDecodeSubtype (n : Nat) : Option SpecTec.subtype :=
  let p := Nat.unpair n
  decodeSubtypeFuel p.1 p.2

theorem fullSubtype_roundtrip (x : SpecTec.subtype) :
    fullDecodeSubtype (fullEncodeSubtype x) = some x := by
  simpa [fullDecodeSubtype, fullEncodeSubtype, Nat.unpair_pair] using
    (fuelRoundtrip (depthSubtype x + 1)).subtype x (Nat.lt_succ_self _)

instance : Encodable SpecTec.subtype :=
  Encodable.ofLeftInjection fullEncodeSubtype fullDecodeSubtype fullSubtype_roundtrip

def fullEncodeRectype (x : SpecTec.rectype) : Nat :=
  Nat.pair (depthRectype x + 1) (encodeRectype x)

def fullDecodeRectype (n : Nat) : Option SpecTec.rectype :=
  let p := Nat.unpair n
  decodeRectypeFuel p.1 p.2

theorem fullRectype_roundtrip (x : SpecTec.rectype) :
    fullDecodeRectype (fullEncodeRectype x) = some x := by
  simpa [fullDecodeRectype, fullEncodeRectype, Nat.unpair_pair] using
    (fuelRoundtrip (depthRectype x + 1)).rectype x (Nat.lt_succ_self _)

instance : Encodable SpecTec.rectype :=
  Encodable.ofLeftInjection fullEncodeRectype fullDecodeRectype fullRectype_roundtrip

def fullEncodeDeftype (x : SpecTec.deftype) : Nat :=
  Nat.pair (depthDeftype x + 1) (encodeDeftype x)

def fullDecodeDeftype (n : Nat) : Option SpecTec.deftype :=
  let p := Nat.unpair n
  decodeDeftypeFuel p.1 p.2

theorem fullDeftype_roundtrip (x : SpecTec.deftype) :
    fullDecodeDeftype (fullEncodeDeftype x) = some x := by
  simpa [fullDecodeDeftype, fullEncodeDeftype, Nat.unpair_pair] using
    (fuelRoundtrip (depthDeftype x + 1)).deftype x (Nat.lt_succ_self _)

instance : Encodable SpecTec.deftype :=
  Encodable.ofLeftInjection fullEncodeDeftype fullDecodeDeftype fullDeftype_roundtrip

example : Encodable SpecTec.module := inferInstance

theorem module_roundtrip_unconditional (m : SpecTec.module) :
    Encodable.decode (Encodable.encode m) = some m := Encodable.encodek m


end properties.wasm_module_not_ok.TypeFamilyCodec
