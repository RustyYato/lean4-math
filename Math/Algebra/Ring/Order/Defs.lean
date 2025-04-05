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
