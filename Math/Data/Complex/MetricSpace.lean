import Math.Data.NNReal.Sqrt
import Math.Algebra.Impls.Complex
import Math.Data.Real.Sqrt

open NNReal

namespace Complex

noncomputable instance : AbsoluteValue ℂ ℝ≥0 where
  abs x := (square x.real + square x.img).sqrt

instance instLawfulAbs : IsLawfulAbs ℂ where
  abs_zero_iff := by
    intro x
    show NNReal.sqrtEquiv _ = 0 ↔ x = 0
    apply Iff.intro
    intro h
    have : sqrtEquiv.symm (sqrtEquiv (square x.real + square x.img)) =
       sqrtEquiv.symm 0 := by rw [h]
    rw [sqrtEquiv.coe_symm, resp_zero] at this
    have ⟨ha, hb⟩ := NNReal.of_add_eq_zero _ _ this
    ext
    exact of_square_eq_zero ha
    exact of_square_eq_zero hb
    rintro rfl
    simp [resp_zero]
  abs_nonneg _ := by apply bot_le
  abs_mul a b := by
    show NNReal.sqrtEquiv _ = NNReal.sqrtEquiv _ * NNReal.sqrtEquiv _
    rw [←resp_mul]
    simp
    congr
    apply Subtype.val_inj
    unfold square
    show (a.real * b.real - a.img * b.img) ^ 2 + (a.real * b.img + a.img * b.real) ^ 2 =
      (a.real ^ 2 + a.img ^ 2) * (b.real ^ 2 + b.img ^ 2)

    simp [mul_add, add_mul, mul_sub, sub_mul, square_sub, mul_npow, npow_two,
      sub_eq_add_neg, neg_add_rev, ←neg_mul_left, ←neg_mul_right, neg_neg]
    ac_nf
    repeat first|rw [add_comm _ (a.img * (a.img * (b.img * b.img)))]|rw [←add_assoc]
    congr 2
    repeat rw [add_assoc]
    congr 1
    repeat first|rw [add_comm _ (a.img * (a.img * (b.real * b.real)))]|rw [←add_assoc]
    repeat rw [add_assoc]
    rw (occs := [2]) [←add_zero (a.img * (a.img * (b.real * b.real)))]
    congr
    rw (occs := [2]) [←add_assoc (-_)]
    rw [neg_add_cancel, zero_add, neg_add_cancel]
  abs_add_le_add_abs a b := by
    show NNReal.sqrt _ ≤ NNReal.sqrt _ + NNReal.sqrt _
    apply NNReal.square_strictMonotone.le_iff_le.mp
    rw [NNReal.sqrt_sq]
    simp [square, square_add, NNReal.sqrt_sq]
    show (a.real ^ 2 + 2 * a.real * b.real + b.real ^ 2) + (a.img ^ 2 + 2 * a.img * b.img + b.img ^ 2)
      ≤ (a.real ^ 2 + a.img ^ 2) + _ + (b.real ^ 2 + b.img ^ 2)
    rw [show
      (a.real ^ 2 + 2 * a.real * b.real + b.real ^ 2) + (a.img ^ 2 + 2 * a.img * b.img + b.img ^ 2) =
      (a.real ^ 2 + a.img ^ 2 + (b.real ^ 2 + b.img ^ 2)) + (2 * a.real * b.real + 2 * a.img * b.img) by ac_rfl]
    rw (occs := [2]) [add_comm_right _ _ (b.real ^ 2 + _)]
    apply add_le_add_left
    rw [mul_assoc _ (NNReal.sqrt _), sqrt_mul]
    show _ ≤ 2 * _
    rw [mul_assoc, mul_assoc, ←mul_add]
    apply Real.mul_le_mul_of_nonneg_left (k := 2)
    apply Real.ofRat_le.mpr; decide
    rcases lt_or_le (a.real * b.real + a.img * b.img) 0 with h | h
    apply le_trans
    exact le_of_lt h
    show 0 ≤ NNReal.sqrt _
    apply bot_le
    apply (Real.square_strictMonotoneOn.le_iff_le _ _).mp
    show _ ≤ Subtype.val (_^2: ℝ≥0)
    rw [sqrt_sq]
    show _ ≤ ((a.real ^ 2 + a.img ^ 2) * (b.real ^ 2 + b.img ^ 2))
    · apply Real.cauchy_schwartz
    · show 0 ≤ a.real * b.real + a.img * b.img
      assumption
    show 0 ≤ NNReal.sqrt _
    apply bot_le
  abs_eq_of_add_eq_zero := by
    intro a b h
    cases neg_eq_of_add_left h; clear h
    show NNReal.sqrt _ = NNReal.sqrt _
    simp [NNReal.square_neg]

noncomputable instance : Dist ℂ ℝ≥0 where
  dist a b := ‖a - b‖

instance : IsMetricSpace ℂ := Abs.instIsMetricSpace ℂ
instance : Topology ℂ := Topology.ofIsPseudoMetricSpace

instance : Topology.IsConnected ℂ where
  univ_preconnected := by
    intro u v hu hv total ⟨x, hx', hx⟩ ⟨y, hy', hy⟩
    rw [Set.univ_inter]; clear hx' hy'
    sorry


end Complex
