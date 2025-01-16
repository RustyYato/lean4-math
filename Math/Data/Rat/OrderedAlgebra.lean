import Math.Data.Rat.Algebra
import Math.Data.Rat.Order
import Math.Algebra.Order

instance : IsStrictOrderedRing ℚ where
  add_le_add_left := by
    intro a b h c
    apply Rat.add_le_add_left.mp
    assumption
  zero_le_one := by decide
  mul_nonneg := by
    intro a b ha hb
    cases lt_or_eq_of_le ha
    cases lt_or_eq_of_le hb
    apply le_of_lt
    apply Rat.mul_pos
    assumption
    assumption
    subst b
    rw [mul_zero]
    subst a
    rw [zero_mul]
  mul_le_mul_of_nonneg_left := by
    exact fun a b a_1 c a_2 => Rat.mul_le_mul_of_left_nonneg a b c a_2 a_1
  mul_le_mul_of_nonneg_right := by
    exact fun a b a_1 c a_2 => Rat.mul_le_mul_of_right_nonneg a b c a_2 a_1
  mul_pos := by
    exact fun a b a_1 a_2 => Rat.mul_pos a_1 a_2
