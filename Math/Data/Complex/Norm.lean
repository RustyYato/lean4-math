import Math.Data.Complex.Defs
import Math.Data.Real.Sqrt

namespace Complex

noncomputable instance : Norm ℂ ℝ where
  norm x :=
    NNReal.embedReal <|
    NNReal.sqrt ((NNReal.square x.real) + (NNReal.square x.img))

def norm_def (x: ℂ) : ‖x‖ =
  NNReal.embedReal (NNReal.sqrt ((NNReal.square x.real) + (NNReal.square x.img))) := rfl

private def norm_mul' (x y: ℂ) : ‖x * y‖ = ‖x‖ * ‖y‖ := by
  simp only [norm_def]; rw [←map_mul NNReal.embedReal]
  congr 1
  rw [NNReal.sqrt_mul]
  congr
  apply NNReal.embedReal.inj
  simp [map_add, map_mul, square_add, square_sub,
    sub_eq_add_neg, mul_npow, mul_add, add_mul]
  rw [←neg_mul_right, mul_assoc, square_neg, mul_npow]
  ac_nf
  rw [add_comm (-_)]
  repeat rw [add_assoc]
  rw [add_neg_cancel, add_zero]

instance : IsAlgebraNorm ℂ where
  norm_zero_iff {a} := by
    rw [norm_def,
      ←map_zero NNReal.embedReal,
      NNReal.embedReal.inj.eq_iff,
      NNReal.sqrt_eq_zero_iff_eq_zero,
      NNReal.add_eq_zero_iff,
      NNReal.square_eq_zero_iff_eq_zero,
      NNReal.square_eq_zero_iff_eq_zero,
      ←map_zero Real.ofRatHom]
    apply Iff.intro
    intro ⟨_, _⟩; ext <;> assumption
    rintro rfl
    apply And.intro <;> rfl
  norm_one := by simp [norm_def, map_one, map_zero]
  norm_neg a := by simp [norm_def, map_neg, NNReal.square_neg]
  norm_mul := norm_mul'
  norm_add_le_add_norm a b := by
    simp only [norm_def]
    rw [←map_add NNReal.embedReal]
    show NNReal.orderEmbedReal _ ≤ NNReal.orderEmbedReal _
    apply (map_le NNReal.orderEmbedReal).mp
    apply NNReal.square_strictMonotone.le_iff_le.mp
    simp [NNReal.sqrt_sq, square_add]
    apply (map_le NNReal.orderEmbedReal).mpr
    show NNReal.embedReal _ ≤ NNReal.embedReal _
    simp [map_add]
    generalize hk:NNReal.embedReal (2 * (NNReal.square a.real + NNReal.square a.img).sqrt * (NNReal.square b.real + NNReal.square b.img).sqrt) = k
    simp [square_add]
    ac_nf
    repeat rw [←add_assoc]
    repeat apply add_le_add_right
    subst hk
    rw [←mul_assoc, ←mul_assoc, ←add_mul, mul_comm _ 2]
    rw [mul_assoc, map_mul, show NNReal.embedReal 2 = 2 from ?_]
    apply mul_le_mul_of_nonneg_left
    rcases lt_or_le (a.img * b.img + a.real * b.real) 0 with g | g
    apply le_trans
    apply le_of_lt; assumption
    rw [←map_zero NNReal.embedReal]
    apply (map_le NNReal.orderEmbedReal).mp
    apply bot_le
    apply (Real.square_strictMonotoneOn.le_iff_le _ _).mp
    rw [←map_npow, mul_npow, NNReal.sqrt_sq, NNReal.sqrt_sq]
    simp [map_mul, map_add]
    rw [add_comm (a.real ^ 2) (a.img ^ 2), add_comm (b.real ^ 2) (b.img ^ 2)]
    apply Real.cauchy_schwartz
    assumption
    show 0 ≤ NNReal.embedReal _
    rw [←map_zero NNReal.embedReal]
    apply (map_le NNReal.orderEmbedReal).mp
    apply bot_le
    apply natCast_nonneg
    rfl

end Complex
