import Math.Data.Real.Div
import Math.Algebra.Group.Order

instance Real.instOrderedRing : IsStrictOrderedSemiring ℝ where
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

def Real.abs_mul' (a b: ℝ) : ‖a * b‖ = ‖a‖ * ‖b‖ := by
  cases a, b with | mk a b =>
  apply Quotient.sound
  apply CauchySeq.pointwise
  intro n
  show ‖a n * b n‖ = ‖a n‖ * ‖b n‖
  rw [Rat.abs_mul]

instance : IsLawfulAbs ℝ where
  abs_nonneg a := by
    rw [Real.abs_def]
    split
    assumption
    rw [←Real.neg_le_neg_iff, neg_neg]
    apply le_of_lt
    rw [lt_iff_not_le]
    assumption
  abs_mul := by apply Real.abs_mul'
  abs_zero_iff {x} := by
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
  abs_eq_of_add_eq_zero := by
    intro a b h
    rw [neg_eq_of_add_right h,
      ←neg_one_mul]
    rw [Real.abs_mul']
    apply one_mul

instance : NeZero (2: ℝ) where
  out := by
    symm; apply ne_of_lt
    exact two_pos

def Real.abs_of_nonneg (a: ℝ) : 0 ≤ a ↔ ‖a‖ = a := by
  apply flip Iff.intro
  · intro h
    rw [←h]
    exact abs_nonneg a
  · intro h
    rw [abs_def]
    split
    rfl
    contradiction
