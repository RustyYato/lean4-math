import Math.Data.Rat.Order
import Math.Algebra.Order
import Math.Algebra.Archimedean.Basic

instance : IsStrictOrderedRing ℚ where
  add_le_add_left := by
    intro a b h c
    apply Rat.add_le_add_left.mp
    assumption
  le_iff_nsmul_le := by
    intro a b n npos
    refine Rat.le_iff_mul_left_pos ?_
    rw [Rat.lt_def, sub_zero]
    apply Int.ofNat_pos.mpr
    exact npos
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

instance : IsOrderedAbsRing ℚ where
  abs_nonneg := Rat.abs_nonneg
  abs_zero := Rat.eq_zero_iff_abs_eq_zero.symm
  abs_add_le_add_abs := Rat.abs_add_le_add_abs
  nsmul_abs _ _ := Rat.abs_mul _ _
  abs_one := rfl
  mul_abs := Rat.abs_mul
  natcast_abs _ := rfl
  intcast_abs _ := rfl
  neg_abs a := by
    rw [neg_eq_neg_one_zsmul, zsmul_eq_intCast_mul,
      Rat.abs_mul]
    apply one_mul
  sub_eq_add_neg := sub_eq_add_neg
  zsmul_ofNat := zsmul_ofNat
  zsmul_negSucc := zsmul_negSucc
  neg_add_cancel := neg_add_cancel

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
