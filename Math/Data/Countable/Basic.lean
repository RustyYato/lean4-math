import Math.Data.Encodable.Basic
import Math.Logic.Equiv.Basic

class inductive IsCountable (α: Sort u): Prop where
| intro (x: α ↪ Nat)



noncomputable section

namespace IsCountable

open Classical

variable {α: Sort*} (x y z: α) {a b c: α} [IsCountable α]

def encode : α ↪ Nat :=
  choice <| match inferInstanceAs (IsCountable α) with | .intro c => ⟨c⟩

def decode (n: Nat) : Option (PLift α) :=
  if h: ∃x: α, encode x = n then
    .some ⟨choose h⟩
  else
    .none

def decode_spec : decode (encode x) = .some ⟨x⟩ := by
  have : ∃y: α, encode y = encode x := ⟨_, rfl⟩
  rw [decode, dif_pos this]
  congr
  apply encode.inj
  show encode _ = encode _
  apply Classical.choose_spec this

def decode_eq_none : decode n (α := α) = .none ↔ ∀x: α, encode x ≠ n := by
  apply Iff.intro
  intro h x g
  rw [decode] at h
  rw [dif_pos ⟨_, g⟩] at h
  contradiction
  intro h
  rw [decode, dif_neg]
  intro ⟨x, g⟩
  apply h x
  assumption

instance : IsCountable Nat := .intro .rfl

def ofEquiv (h: α ≃ β) : IsCountable β := by
  apply IsCountable.intro
  rename_i g
  exact Equiv.congrEmbed h .rfl encode

def ofEmbed (h: β ↪ α) : IsCountable β := by
  apply IsCountable.intro
  rename_i g
  exact h.trans encode

end IsCountable

namespace IsCountable

instance [h: Encodable α] : IsCountable α := .intro ⟨h.encode, encode_inj⟩

def encodable (α: Type*) [IsCountable α] : Encodable α where
  encode := encode
  decode' n := match decode n with
    | .some ⟨x⟩ => .some x
    | .none => .none
  spec := by
    intro x
    rw [decode_spec]

example : ¬IsCountable (Nat -> Bool) := by
  intro c
  exact Encodable.cantor_diag (encodable (Nat -> Bool))

end IsCountable

end
