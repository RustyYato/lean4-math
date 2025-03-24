import Math.Data.Rat.Order
import Math.Algebra.Archimedean.Basic
import Math.Algebra.Abs.Defs

instance : IsStrictOrderedSemiring ℚ where
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

instance : IsLawfulAbs ℚ where
  abs_nonneg := Rat.abs_nonneg
  abs_zero_iff := Rat.eq_zero_iff_abs_eq_zero.symm
  abs_add_le_add_abs := Rat.abs_add_le_add_abs
  abs_mul := Rat.abs_mul
  abs_eq_of_add_eq_zero := by
    intro a b h
    rw [neg_eq_of_add_right h, ←neg_one_mul,
      Rat.abs_mul]
    apply one_mul

instance : Archimedean ℚ := by
  apply archimedean_iff_nat_lt.mpr
  intro x
  exists (x.ceil + 1).natAbs
  apply flip lt_of_lt_of_le
  show ((x.ceil + 1: ℤ): ℚ) ≤ _
  rw [←intCast_ofNat, Rat.intCast_le]
  apply Int.le_natAbs
  apply lt_of_le_of_lt
  apply Rat.self_le_ceil
  rw [Rat.intCast_lt]
  exact Int.lt_succ x.ceil
