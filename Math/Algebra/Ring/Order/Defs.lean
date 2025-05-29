import Math.Algebra.Ring.Defs
import Math.Algebra.Semiring.Order.Defs
import Math.Algebra.Group.Order

variable [RingOps α] [IsRing α] [LE α] [LT α] [IsStrictOrderedSemiring α]
  [IsNontrivial α]

def square_nonneg [IsLinearOrder α]: ∀a: α, 0 ≤ a ^ 2 := by
  intro a
  cases le_total 0 a
  rw [npow_two]
  apply mul_nonneg
  assumption
  assumption
  rw [←square_neg a]
  rename_i h
  rw [neg_le_neg_iff, neg_zero] at h
  rw [npow_two]
  apply mul_nonneg
  assumption
  assumption

def eq_zero_of_square_eq_zero [IsLinearOrder α] {a: α}: a ^ 2 = 0 -> a = 0 := by
  intro g
  rcases lt_trichotomy 0 a with h | h | h
  have : 0 < a ^ 2 := square_pos a h
  rw [g] at this
  exact (lt_irrefl this).elim
  symm; assumption
  have : 0 < (-a) ^ 2 := square_pos (-_) ?_
  rw [square_neg, g] at this
  exact (lt_irrefl this).elim
  rwa [neg_lt_neg_iff, neg_neg, neg_zero]

def intCast_strictmonotone : StrictMonotone (Int.cast (R := α)) := by
  intro a b h
  cases a with
  | ofNat a =>
    cases b with
    | ofNat b =>
      rw [intCast_ofNat, intCast_ofNat]
      apply natCast_strictmonotone
      apply Int.ofNat_lt.mp
      assumption
    | negSucc b => contradiction
  | negSucc a =>
    cases b with
    | ofNat b =>
      rw [intCast_negSucc, intCast_ofNat]
      rw [←zero_add (-_), ←sub_eq_add_neg, sub_lt_iff_lt_add,
        ←natCast_add, Nat.add_succ, natCast_succ]
      apply lt_of_lt_of_le
      apply zero_lt_one
      rw (occs := [1]) [←zero_add 1]
      apply add_le_add_right
      apply natCast_nonneg
    | negSucc b =>
      rw [intCast_negSucc,intCast_negSucc, ←neg_lt_neg_iff]
      apply natCast_strictmonotone
      omega

def intCast_le {a b: ℤ} : (a: α) ≤ b ↔ a ≤ b :=
  intCast_strictmonotone.le_iff_le

def abs_intCast_eq_intCast_abs [Max α] [Min α] [IsLinearLattice α] (a: ℤ) : (|a|: ℤ) = (|a|: α) := by
  open scoped Classical in
  unfold abs
  apply le_antisymm
  apply le_max_iff.mpr
  rw [max_def]; split
  rw [←intCast_neg]
  right; rfl
  left ; rfl
  rw [max_def]
  split <;> rename_i h
  rw [intCast_neg]
  rw [max_def, if_pos]
  rwa [intCast_neg, intCast_le] at h
  rw [max_def, if_neg]
  rwa [intCast_neg, intCast_le] at h
