import Math.Type.Notation
import Math.Logic.Basic
import Math.Order.Dual
import Math.Relation.Basic

class IsPreOrder (α: Type*) [LT α] [LE α]: Prop where
  lt_iff_le_and_not_le: ∀{a b: α}, a < b ↔ a ≤ b ∧ ¬b ≤ a
  le_refl: ∀a: α, a ≤ a
  le_trans: ∀{a b c: α}, a ≤ b -> b ≤ c -> a ≤ c

variable {α: Type*} {a b c d: α}
variable [LT α] [LE α] [IsPreOrder α]

@[refl, simp]
def le_refl: ∀a: α, a ≤ a := IsPreOrder.le_refl
def lt_iff_le_and_not_le: a < b ↔ a ≤ b ∧ ¬b ≤ a := IsPreOrder.lt_iff_le_and_not_le
def le_trans: a ≤ b -> b ≤ c -> a ≤ c := IsPreOrder.le_trans

def le_of_lt: a < b -> a ≤ b := fun h => (lt_iff_le_and_not_le.mp h).left
def lt_of_le_of_not_le : a ≤ b -> ¬(b ≤ a) -> a < b := (lt_iff_le_and_not_le.mpr ⟨·, ·⟩)

def le_of_eq: a = b -> a ≤ b := fun h => h ▸ le_refl _
def not_le_of_lt (hab : a < b) : ¬ b ≤ a := (lt_iff_le_and_not_le.1 hab).2
def not_lt_of_le (hab : a ≤ b) : ¬ b < a := imp_not_comm.1 not_le_of_lt hab
def lt_irrefl: ¬a < a := fun h => (lt_iff_le_and_not_le.mp h).right (le_refl _)
def ne_of_lt: a < b -> a ≠ b := fun h g => lt_irrefl (g ▸ h)
def le_of_lt_or_eq: a < b ∨ a = b -> a ≤ b := by
  intro h
  cases h
  apply le_of_lt; assumption
  apply le_of_eq; assumption
def lt_trans : a < b -> b < c -> a < c := by
  intro ab bc
  replace ⟨ab, nba⟩ := lt_iff_le_and_not_le.mp ab
  replace ⟨bc, ncb⟩ := lt_iff_le_and_not_le.mp bc
  apply lt_iff_le_and_not_le.mpr ⟨le_trans ab bc, _⟩
  intro h
  apply nba
  apply le_trans
  assumption
  assumption
def lt_of_lt_of_le : a < b -> b ≤ c -> a < c := by
  intro ab bc
  replace ⟨ab, nba⟩ := lt_iff_le_and_not_le.mp ab
  apply lt_iff_le_and_not_le.mpr ⟨le_trans ab bc, _⟩
  intro h
  apply nba
  apply le_trans
  assumption
  assumption
def lt_of_le_of_lt : a ≤ b -> b < c -> a < c := by
  intro ab bc
  replace ⟨bc, ncb⟩ := lt_iff_le_and_not_le.mp bc
  apply lt_iff_le_and_not_le.mpr ⟨le_trans ab bc, _⟩
  intro h
  apply ncb
  apply le_trans
  assumption
  assumption

def lt_asymm : a < b -> b < a -> False := (lt_irrefl <| lt_trans · ·)

instance [IsPreOrder α] : IsPreOrder (OrderDual α) where
  lt_iff_le_and_not_le := by
    intro a b
    apply Iff.trans (lt_iff_le_and_not_le (α := α))
    rfl
  le_refl := le_refl (α := α)
  le_trans := flip (le_trans (α := α))

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

instance [DenselyOrdered α] : DenselyOrdered (OrderDual α) where
  dense := by
    intro a b a_lt_b
    have h := dense (α := α) _ _ a_lt_b
    obtain ⟨x, _, _⟩ := h
    exists x

instance [NoBotOrder α] : NoTopOrder (OrderDual α) where
  exists_not_le := by
    intro x
    have ⟨b, _⟩ := exists_not_ge x.get
    exists b

instance [NoTopOrder α] : NoBotOrder (OrderDual α) where
  exists_not_ge := by
    intro x
    have ⟨b, _⟩ := exists_not_le x.get
    exists b

instance [NoMinOrder α] : NoMaxOrder (OrderDual α) where
  exists_gt := by
    intro x
    have ⟨b, _⟩ := exists_lt x.get
    exists b

instance [NoMaxOrder α] : NoMinOrder (OrderDual α) where
  exists_lt := by
    intro x
    have ⟨b, _⟩  := exists_gt x.get
    exists b

instance : @Relation.IsTrans α (· < ·) where
  trans := lt_trans
instance : @Relation.IsTrans α (· ≤ ·) where
  trans := le_trans
instance : @Relation.IsIrrefl α (· < ·) where
  irrefl := lt_irrefl
