import Math.Algebra.Monoid.Order.Defs
import Math.Algebra.Group.Defs

instance [LE α] [LT α] [AddGroupOps α] [IsOrderedAddCommMonoid α] [IsAddGroup α] : IsOrderedCancelAddCommMonoid α where
  le_of_add_le_add_left := by
    intro k a b h
    have := add_le_add_left _ _ h (-k)
    rwa [←add_assoc, ←add_assoc, neg_add_cancel, zero_add, zero_add] at this

instance [LE α] [LT α] [GroupOps α] [IsOrderedCommMonoid α] [IsGroup α] : IsOrderedCancelCommMonoid α where
  le_of_mul_le_mul_left := le_of_add_le_add_left (α := AddOfMul α)

section

variable [LE α] [LT α] [AddGroupOps α] [IsAddGroup α] [IsOrderedAddCommMonoid α]

def lt_of_add_lt_add_left: ∀a b c: α, a + b < a + c → b < c := by
  intro a b c h
  have := add_lt_add_left (a + b) (a + c) (-a) h
  rwa [←add_assoc, ←add_assoc, neg_add_cancel, zero_add, zero_add] at this

def lt_of_add_lt_add_right: ∀a b c: α, a + c < b + c → a < b := by
  intro a b c h
  have := add_lt_add_right (a + c) (b + c) (-c) h
  rwa [add_assoc, add_assoc, add_neg_cancel, add_zero, add_zero] at this

def sub_le_iff_le_add (a b c: α) : a - b ≤ c ↔ a ≤ c + b := by
  apply Iff.intro
  intro h
  apply le_of_add_le_add_right
  show a + -b ≤ _
  rwa [add_assoc, add_neg_cancel, add_zero, ←sub_eq_add_neg]
  intro h
  apply le_of_add_le_add_right
  rwa [sub_add_cancel]

def le_add_iff_sub_le (a b c: α) : a ≤ b + c ↔ a - c ≤ b := by
  symm; apply sub_le_iff_le_add

def le_sub_iff_add_le (a b c: α) : a ≤ b - c ↔ a + c ≤ b := by
  apply Iff.intro
  intro h
  apply le_of_add_le_add_right
  show a + c + -c ≤ _
  rwa [add_assoc, add_neg_cancel, add_zero, ←sub_eq_add_neg]
  intro h
  apply le_of_add_le_add_right
  rwa [sub_add_cancel]

def add_le_iff_le_sub (a b c: α) : a + b ≤ c ↔ a ≤ c - b := by
  symm; apply le_sub_iff_add_le

def sub_lt_iff_lt_add (a b c: α) : a - b < c ↔ a < c + b := by
  apply Iff.intro
  intro h
  apply lt_of_add_lt_add_right
  show a + -b < _
  rwa [add_assoc, add_neg_cancel, add_zero, ←sub_eq_add_neg]
  intro h
  apply lt_of_add_lt_add_right
  rwa [sub_add_cancel]

def lt_add_iff_sub_lt (a b c: α) : a < b + c ↔ a - c < b := by
  symm; apply sub_lt_iff_lt_add

def lt_sub_iff_add_lt (a b c: α) : a < b - c ↔ a + c < b := by
  apply Iff.intro
  intro h
  apply lt_of_add_lt_add_right
  show a + c + -c < _
  rwa [add_assoc, add_neg_cancel, add_zero, ←sub_eq_add_neg]
  intro h
  apply lt_of_add_lt_add_right
  rwa [sub_add_cancel]

def add_lt_iff_lt_sub (a b c: α) : a + b < c ↔ a < c - b := by
  symm; apply lt_sub_iff_add_lt

def neg_le_neg (a b: α) : a ≤ b -> -b ≤ -a := by
  intro h
  apply le_of_add_le_add_left
  rw [add_neg_cancel]
  apply le_of_add_le_add_right
  rwa [add_assoc, neg_add_cancel, add_zero, zero_add]

def neg_le_neg_iff {a b: α} : a ≤ b ↔ -b ≤ -a := by
  apply Iff.intro
  apply neg_le_neg
  intro h
  rw [←neg_neg a, ←neg_neg b]
  apply neg_le_neg
  assumption

def neg_lt_neg (a b: α) : a < b -> -b < -a := by
  intro h
  apply lt_of_add_lt_add_left
  rw [add_neg_cancel]
  apply lt_of_add_lt_add_right
  rwa [add_assoc, neg_add_cancel, add_zero, zero_add]

def neg_lt_neg_iff {a b: α} : a < b ↔ -b < -a := by
  apply Iff.intro
  apply neg_lt_neg
  intro h
  rw [←neg_neg a, ←neg_neg b]
  apply neg_lt_neg
  assumption

def neg_le_of_nonneg (a: α) : 0 ≤ a -> -a ≤ a := by
  intro h
  apply le_trans _ h
  rw [←neg_zero]; apply neg_le_neg
  assumption

def le_neg_of_nonpos (a: α) : a ≤ 0 -> a ≤ -a := by
  intro h
  apply le_trans h
  rw [←neg_zero]; apply neg_le_neg
  assumption

def neg_le_self [IsLinearOrder α] {a: α} : -a ≤ a ↔ 0 ≤ a := by
  apply flip Iff.intro
  apply neg_le_of_nonneg
  intro h
  have := add_le_add_left _ _ h  a
  rw [add_neg_cancel] at this
  rw [←not_lt]
  intro h
  have g := add_lt_add_left _ _ a h
  rw [add_zero] at g
  have := lt_asymm (lt_of_le_of_lt this g)
  contradiction

def le_neg_self [IsLinearOrder α] {a: α} : a ≤ -a ↔ a ≤ 0 := by
  rw (occs := [1]) [←neg_neg a, neg_le_self, ←neg_zero, ←neg_le_neg_iff]

end
