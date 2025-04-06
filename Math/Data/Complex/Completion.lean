import Math.Data.Complex.Norm

notation "ℚ[i]" => @Rsqrtd ℚ (-1)

private def toℂ : ℚ[i] ↪+* ℂ where
  toFun x := .mk x.a x.b
  inj' := by
    intro x y h
    simp at h
    have := Rsqrtd.mk.inj h
    rw [Rat.cast.inj.eq_iff, Rat.cast.inj.eq_iff] at this
    ext; exact this.left; exact this.right
  map_zero := rfl
  map_one := rfl
  map_add := rfl
  map_mul := rfl

noncomputable instance : Norm ℚ[i] ℝ where
  norm x := ‖toℂ x‖

private def norm_def (q: ℚ[i]) : ‖q‖ = ‖toℂ q‖ := rfl

instance : IsAlgebraNorm ℚ[i] where
  norm_zero_iff {a} := by rw [norm_def, norm_zero_iff, ←map_zero toℂ, toℂ.inj.eq_iff]
  norm_one := by rw [norm_def, map_one, norm_one]
  norm_neg _ := by rw [norm_def, map_neg, norm_neg]; rfl
  norm_mul _ _ := by rw [norm_def, map_mul, norm_mul]; rfl
  norm_add_le_add_norm a b := by
    rw [norm_def, map_add]
    apply norm_add_le_add_norm

abbrev ℝi := Cauchy ℚ[i]

-- show that the complex numbers are the completion of the gaussian rationals
def equivℂ : ℝi ≃+* ℂ where
  toFun := sorry
  invFun := sorry
  leftInv := sorry
  rightInv := sorry
  map_zero := sorry
  map_one := sorry
  map_add := sorry
  map_mul := sorry
