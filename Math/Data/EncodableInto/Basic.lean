import Math.Type.Basic
import Math.Function.Basic
import Math.Data.Fintype.Basic

class EncodableInto (α β: Type*) where
  encode_into: α -> β
  decode_from': β -> Option α
  spec_decode_from': ∀x, decode_from' (encode_into x) = x

export EncodableInto (encode_into)

open EncodableInto

def encode_into_inj [h: EncodableInto α β] : Function.Injective (encode_into (α := α) (β := β)) := by
  intro a b eq
  apply Option.some.inj
  rw [←h.spec_decode_from', ←h.spec_decode_from', eq]

def EncodableInto.decEq [DecidableEq β] [h: EncodableInto α β] : DecidableEq α :=
  fun x y => decidable_of_iff (encode_into (β := β) x = encode_into y) <| by
    apply flip Iff.intro
    intro h; rw [h]
    apply encode_into_inj

def decode_from [DecidableEq β] [h: EncodableInto α β] (val: β) : Option α :=
  match EncodableInto.decode_from' val with
  | .none => .none
  | .some x =>
    if encode_into x = val then
      .some x
    else
      .none

def spec_decode_from [DecidableEq β] [h: EncodableInto α β] (val: α) : ∀{enc: β}, encode_into val = enc ↔ decode_from enc = .some val := by
  intro enc
  apply Iff.intro
  intro h
  subst enc
  unfold decode_from
  rw [spec_decode_from']
  dsimp
  rw [if_pos rfl]
  intro h
  unfold decode_from at h
  split at h
  contradiction
  split at h
  subst enc; cases h
  rfl
  contradiction

instance : EncodableInto α α where
  encode_into := id
  decode_from' x := x
  spec_decode_from' _ := rfl

instance : EncodableInto (Fin n) Nat where
  encode_into := Fin.val
  decode_from' x := if h:x < n then .some ⟨_, h⟩ else .none
  spec_decode_from' x := by
    dsimp
    rw [if_pos x.isLt]

def Fintype.ofEncodableIntoFin [enc: EncodableInto α (Fin n)] : Fintype α where
  all := (Fintype.all: List (Fin n)).filterMap decode_from
  nodup := by
    apply List.nodup_filterMap
    apply Fintype.nodup
    intro x y hx eq
    have hx' := (spec_decode_from (α := α) (β := Fin n) ((decode_from x).get (by assumption))).mpr (by rw [Option.some_get])
    have hy' := (spec_decode_from (α := α) (β := Fin n) ((decode_from y).get (by rw [←eq]; assumption))).mpr (by rw [Option.some_get])
    rw [←hx', ←hy']
    congr 2
  complete := by
    intro x
    apply List.mem_filterMap.mpr
    refine ⟨_, ?_, (spec_decode_from _).mp rfl⟩
    apply Fintype.complete
