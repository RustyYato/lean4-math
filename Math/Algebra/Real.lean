import Math.Algebra.Ring
import Math.Algebra.Rat
import Math.Data.Real.Div

namespace Real

instance : RatCast ℝ where
  cast := .ofRat
instance : SMul ℕ ℝ where
  smul n r := n * r
instance : SMul ℤ ℝ where
  smul n r := n * r
instance : SMul ℚ ℝ where
  smul n r := n * r

instance : Pow ℝ ℕ where
  pow := flip npowRec

instance : CheckedIntPow ℝ (· ≠ 0) where
  checked_pow x n h := match n with
  | .ofNat n => x ^ n
  | .negSucc n =>
    have := h.resolve_right (by apply not_le_of_lt; exact Int.negSucc_lt_zero _)
    x⁻¹? ^ n.succ

instance : IsField ℝ where
  add_comm := Real.add_comm
  add_assoc := Real.add_assoc
  zero_add := Real.zero_add
  add_zero := Real.add_zero
  mul_comm := Real.mul_comm
  mul_assoc := Real.mul_assoc
  zero_mul := Real.zero_mul
  mul_zero := Real.mul_zero
  one_mul := Real.one_mul
  mul_one := Real.mul_one
  zero_nsmul := Real.zero_mul
  succ_nsmul := by
    rintro n a
    show ⟦.ofRat (n + 1: Nat)⟧ * a = ⟦.ofRat (.ofNat n)⟧ * a + a
    rw [natCast_succ]
    show (n + 1) * a = n * a + a
    rw [Real.add_mul, Real.one_mul]
  natCast_zero := rfl
  natCast_succ := by
    intro n
    show ⟦.ofRat n.succ⟧ = _
    rw [natCast_succ]
    rfl
  intCast_ofNat _ := rfl
  intCast_negSucc _ := rfl
  ofNat_eq_natCast _ := rfl
  left_distrib _ _ _ := Real.mul_add _ _ _
  right_distrib _ _ _ := Real.add_mul _ _ _
  sub_eq_add_neg a b := by
    cases a, b with | mk a b =>
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro n
    show a n - b n = a n + -b n
    rw [Rat.sub_eq_add_neg]
  zsmul_ofNat _ _ := rfl
  zsmul_negSucc := by
    rintro n ⟨x⟩
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro m
    show (Rat.ofInt _ * x m) = -(Rat.ofInt _ * x m)
    rw [Rat.neg_mul_left]
    rfl
  neg_add_cancel a := by
    rw [Real.add_comm, Real.add_neg_self]
  mul_inv?_cancel := Real.mul_inv_self
  div?_eq_mul_inv? _ _ _ := rfl
  zpow?_ofNat _ _ := rfl
  zpow?_negSucc _ _ _ := rfl
  zero_ne_one := by
    apply ne_of_lt
    show (1 - 0: ℝ).IsPos
    rw [sub_zero]
    exists 1
    apply And.intro
    decide
    exists 0
    intro _ _
    rfl

instance : IsRatAlgebra ℝ where
  rsmul_eq_cast_mul _ _ := rfl
  eq_zero_of_natCast_eq_zero n h := by
    cases n; rfl
    rw [natCast_add] at h
    rename_i n
    exfalso
    rw [natCast_one] at h
    replace h := neg_eq_of_add_right h
    suffices -1 < (n: ℝ) by
      rw [h]at this
      exact lt_irrefl this
    clear h
    exists 1
    apply And.intro
    decide
    exists 0
    intro m hm
    show 1 ≤ Rat.ofNat n - -1
    rw [Rat.sub_eq_add_neg (Rat.ofNat n) (-1), Rat.neg_neg]
    show 1 ≤ (n: ℚ) + ((1: Nat): ℚ)
    rw [←natCast_add, Rat.le_def]
    show 1 * 1 ≤ ((n + 1: Nat): Int) * 1
    rw [Int.one_mul, Int.mul_one]
    apply Int.ofNat_le.mpr
    apply Nat.le_add_left
  ratCast_eq_intCast_div?_natCast q := by
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro n
    show q = (q.num: ℚ) * _
    rw [CauchySeq.inv]; dsimp
    rw [dif_neg]
    rw [←div?_eq_mul_inv?]
    apply ratCast_eq_intCast_div?_natCast

instance : AlgebraMap ℚ ℝ := inferInstance
instance : IsAlgebra ℚ ℝ := inferInstance

end Real
