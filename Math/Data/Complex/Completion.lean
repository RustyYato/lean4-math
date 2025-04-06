import Math.Data.Complex.Defs
import Math.Data.Real.Sqrt

notation "ℚ[i]" => @Rsqrtd ℚ (-1)

noncomputable instance : Norm ℚ[i] ℝ≥0 where
  norm x := NNReal.sqrt ((NNReal.square x.a) + (NNReal.square x.b))

private def norm_def (x: ℚ[i]) : ‖x‖ = NNReal.sqrt ((NNReal.square (Real.ofRatHom x.a)) + (NNReal.square (Real.ofRatHom x.b))) := rfl

private def norm_mul' (x y: ℚ[i]) : ‖x * y‖ = ‖x‖ * ‖y‖ := by
  simp [norm_def]
  rw [←neg_mul_left, ←sub_eq_add_neg]
  simp [map_add, map_sub, map_mul]
  obtain ⟨w, x⟩ := x
  obtain ⟨y, z⟩ := y
  simp
  generalize Real.ofRatHom w = w
  generalize Real.ofRatHom x = x
  generalize Real.ofRatHom y = y
  generalize Real.ofRatHom z = z
  rw [NNReal.sqrt_mul]
  congr
  apply NNReal.embedReal.inj
  simp [map_add, map_mul, square_add, square_sub,
    sub_eq_add_neg, mul_npow, mul_add, add_mul]
  ac_nf
  congr
  rw [←neg_mul_left, ←neg_mul_right, ←neg_mul_right]
  ac_nf
  rw [←add_assoc, neg_add_cancel, zero_add,
    square_neg, mul_npow]

instance : IsAlgebraNorm ℚ[i] where
  norm_zero_iff {a} := by
    rw [norm_def, NNReal.sqrt_eq_zero_iff_eq_zero,
      NNReal.add_eq_zero_iff,
      NNReal.square_eq_zero_iff_eq_zero,
      NNReal.square_eq_zero_iff_eq_zero,
      ←map_zero Real.ofRatHom,
      Real.ofRatHom.inj.eq_iff,
      Real.ofRatHom.inj.eq_iff]
    apply Iff.intro
    intro ⟨_, _⟩; ext <;> assumption
    rintro rfl
    apply And.intro <;> rfl
  norm_one := by simp [norm_def, map_one, map_zero]
  norm_neg a := by simp [norm_def, map_neg, NNReal.square_neg]
  norm_mul := norm_mul'
  norm_add_le_add_norm a b := by
    sorry

-- #synth FieldOps (Cauchy ℚ[i])
