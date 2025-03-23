import Math.Order.Defs
import Math.Order.Monotone

-- do not use this in bounds directly, this is only meant to be used to create a PreOrder
-- for example, via `GaloisConnection`
class PreOrder (α: Type*) extends LT α, LE α, IsPreOrder α

variable {α: Type*} {a b c d: α}
variable [LT α] [LE α] [IsPreOrder α]

class DenselyOrdered (α : Type*) [LT α] : Prop where
  dense : ∀ a₁ a₂ : α, a₁ < a₂ → ∃ a, a₁ < a ∧ a < a₂

class NoBotOrder (α : Type*) [LE α] : Prop where
  exists_not_ge (a : α) : ∃ b, ¬a ≤ b

class NoTopOrder (α : Type*) [LE α] : Prop where
  exists_not_le (a : α) : ∃ b, ¬b ≤ a

class NoMaxOrder (α : Type*) [LT α] : Prop where
  exists_gt (a : α) : ∃ b, a < b

class NoMinOrder (α : Type*) [LT α] : Prop where
  exists_lt (a : α) : ∃ b, b < a

def dense [DenselyOrdered α] : ∀ a₁ a₂ : α, a₁ < a₂ → ∃ a, a₁ < a ∧ a < a₂ := DenselyOrdered.dense
def exists_gt [NoMaxOrder α] (a : α) : ∃ b, a < b := NoMaxOrder.exists_gt _
def exists_lt [NoMinOrder α] (a : α) : ∃ b, b < a := NoMinOrder.exists_lt _

def exists_not_ge [NoBotOrder α] (a : α) : ∃ b, ¬a ≤ b := NoBotOrder.exists_not_ge _
def exists_not_le [NoTopOrder α] (a : α) : ∃ b, ¬b ≤ a := NoTopOrder.exists_not_le _

instance {P: α -> Prop} : LT (Subtype P) where
  lt a b := a.val < b.val
instance {P: α -> Prop} : LE (Subtype P) where
  le a b := a.val ≤ b.val

instance [DenselyOrdered α] : DenselyOrdered αᵒᵖ where
  dense := by
    intro a b a_lt_b
    have h := dense (α := α) _ _ a_lt_b
    obtain ⟨x, _, _⟩ := h
    exists x

instance [NoBotOrder α] : NoTopOrder αᵒᵖ where
  exists_not_le := by
    intro x
    have ⟨b, _⟩ := exists_not_ge x.get
    exists b

instance [NoTopOrder α] : NoBotOrder αᵒᵖ where
  exists_not_ge := by
    intro x
    have ⟨b, _⟩ := exists_not_le x.get
    exists b

instance [NoMinOrder α] : NoMaxOrder αᵒᵖ where
  exists_gt := by
    intro x
    have ⟨b, _⟩ := exists_lt x.get
    exists b

instance [NoMaxOrder α] : NoMinOrder αᵒᵖ where
  exists_lt := by
    intro x
    have ⟨b, _⟩  := exists_gt x.get
    exists b

namespace Pi

variable {β: α -> Sort _}

instance [∀x, LE (β x)] : LE (∀x, β x) where
  le f g := ∀x, f x ≤ g x

instance [∀x, LE (β x)] : LT (∀x, β x) where
  lt f g := f ≤ g ∧ ¬g ≤ f

instance [∀x, LE (β x)] [∀x, LT (β x)] [∀x, IsPreOrder (β x)] : IsPreOrder (∀x, β x) where
  lt_iff_le_and_not_le := Iff.rfl
  le_refl := by
    intro f x
    apply le_refl
  le_trans := by
    intro a b c ab bc x
    apply le_trans
    apply ab
    apply bc

end Pi

variable {β γ: Type*} {x y z: β} {f: α -> β} {g: β -> γ }
variable [LT β] [LE β] [IsPreOrder β]
variable [LT γ] [LE γ] [IsPreOrder γ]

variable {s t: Set α}

namespace Monotone

def const (x: β) : Monotone (fun _: α => x) :=
  fun _ _ _ => le_refl _

end Monotone
