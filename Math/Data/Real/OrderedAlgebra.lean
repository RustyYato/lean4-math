import Math.Algebra.Order
import Math.Data.Rat.OrderedAlgebra
import Math.Data.Real.Div

instance Real.instOrderedRing : IsStrictOrderedRing ℝ where
  zero_le_one := by
    left
    exists 1
    apply And.intro
    decide
    exists 0
    intro _ _
    show 1 ≤ 1 - 0
    rw [sub_zero]
  add_le_add_left := by
    intro a b ab k
    apply Real.le_iff_add_le_add_left.mp
    assumption
  le_iff_nsmul_le := by
    intro a b n npos
    apply Real.le_iff_mul_le_mul_of_pos_left
    show (0: ℕ) < (n: ℝ)
    rw [←Real.lt_iff_natCast_lt]
    assumption
  mul_le_mul_of_nonneg_left a b h k knonneg := by
    cases lt_or_eq_of_le knonneg
    rw [←Real.le_iff_mul_le_mul_of_pos_left]
    assumption
    assumption
    subst k
    rw [zero_mul, zero_mul]
  mul_le_mul_of_nonneg_right a b h k knonneg := by
    cases lt_or_eq_of_le knonneg
    rw [←Real.le_iff_mul_le_mul_of_pos_right]
    assumption
    assumption
    subst k
    rw [mul_zero, mul_zero]
  mul_nonneg a b ha hb := by
    rcases lt_or_eq_of_le ha  with ha | ha
    rcases lt_or_eq_of_le hb with hb | hb
    apply le_of_lt
    rw [Real.zero_lt_iff_pos]
    apply Real.mul_pos_of_pos_of_pos
    <;> (rw [←Real.zero_lt_iff_pos]; assumption)
    subst b; rw [mul_zero]
    subst a; rw [zero_mul]
  mul_pos a b := by
    intro apos bpos
    cases a, b with | mk a b =>
    rw [Real.zero_lt_iff_pos] at apos bpos
    obtain ⟨A, Apos, Aeven⟩ := apos
    obtain ⟨B, Bpos, Beven⟩ := bpos
    have ⟨k, even⟩  := Aeven.merge Beven
    rw [Real.zero_lt_iff_pos]
    exists A * B
    apply And.intro
    apply Rat.mul_pos <;> assumption
    exists k
    intro n hn
    replace ⟨Aeven, Beven⟩ := even n hn
    clear even
    apply Rat.mul_le_mul_nonneg
    apply le_of_lt; assumption
    assumption
    apply le_of_lt; assumption
    assumption

instance : IsOrderedAbsMonoid ℝ where
  abs_nonneg a := by
    rw [Real.abs_def]
    split
    assumption
    rw [←Real.neg_le_neg_iff, neg_neg]
    apply le_of_lt
    rw [lt_iff_not_le]
    assumption
  abs_one := rfl
  mul_abs := by
    intro a b
    cases a, b with | mk a b =>
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro n
    show ‖a n * b n‖ = ‖a n‖ * ‖b n‖
    rw [Rat.abs_mul]

instance : IsOrderedAbsAddGroupWithOne ℝ where
  abs_zero {x} := by
    rw [Real.abs_def]
    split
    rfl
    rw [←neg_zero]
    apply Iff.trans neg_inj
    rfl
  abs_add_le_add_abs a b := by
    cases a, b with | mk a b =>
    apply CauchySeq.le_pointwise
    intro n
    apply Rat.abs_add_le_add_abs
  nsmul_abs a n := by
    cases a with | mk a =>
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro m
    apply nsmul_abs
  natcast_abs n := by
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro m
    apply natcast_abs
  intcast_abs n := by
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro m
    apply intcast_abs
  neg_abs a := by
    cases a with | mk a =>
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro m
    apply neg_abs

  zsmul_ofNat := zsmul_ofNat
  zsmul_negSucc := zsmul_negSucc
  neg_add_cancel := neg_add_cancel
  sub_eq_add_neg := sub_eq_add_neg

instance : IsOrderedAbsRing ℝ := inferInstance

instance : NeZero (2: ℝ) where
  out := by
    symm; apply ne_of_lt
    exact two_pos
