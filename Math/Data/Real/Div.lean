import Math.Data.Real.Order

local notation "⟦" f "⟧" => Real.mk f

def CauchySeq.inv.spec_pos (a b: CauchySeq) (ha: a.IsPos) : a ≈ b ->
  is_cauchy_equiv (fun n => if h:a n = 0 then 0 else (a n)⁻¹) (fun n => if h:b n = 0 then 0 else (b n)⁻¹) := by
  intro ab ε ε_pos
  have hb := IsPos.spec  _ _ ab ha
  obtain ⟨A, A_pos, ha⟩ := ha
  obtain ⟨B, B_pos, hb⟩ := hb
  simp
  obtain ⟨δ, prf⟩ := ha.to₂_left.merge <| hb.to₂_right.merge (ab _ (Rat.mul_pos ε_pos (Rat.mul_pos (Rat.half_pos A_pos) (Rat.half_pos B_pos))))
  refine ⟨δ, ?_⟩
  intro n m δn δm
  have ⟨A_le_an, B_le_bm, eqv⟩ := prf _ _ δn δm
  have : a n ≠ 0 := by
    intro h
    rw [h] at A_le_an
    exact lt_irrefl (lt_of_le_of_lt A_le_an A_pos)
  have : b m ≠ 0 := by
    intro h
    rw [h] at B_le_bm
    exact lt_irrefl (lt_of_le_of_lt B_le_bm B_pos)
  rw [dif_neg, dif_neg]
  rw [Rat.inv_sub_inv, Rat.abs_div]
  rw [Rat.abs_sub_comm]
  by_cases h:a n - b m = 0
  erw [h, Rat.div_eq_mul_inv, Rat.zero_mul]
  assumption
  apply (Rat.lt_of_mul_right_pos _).mpr
  apply lt_trans _ eqv
  · assumption
  · assumption
  · rw [Rat.div_eq_mul_inv, Rat.mul_assoc]
    apply Rat.pos_mul_lt_of_right_lt_one
    apply Rat.abs_pos
    assumption
    rw [←Rat.abs_inv, Rat.inv_mul, Rat.abs_mul,
      ←Rat.abs_of_pos _ (Rat.half_pos A_pos), ←Rat.abs_of_pos _ (Rat.half_pos B_pos)]
    suffices ‖A/?2‖ *‖(a n)⁻¹‖ * (‖B/?2‖ * ‖(b m)⁻¹‖) < 1 by
      apply lt_of_le_of_lt _ this
      assumption
      assumption
      apply le_of_eq
      ac_rfl
    rw [←Rat.abs_mul, ←Rat.abs_mul, ←Rat.div_eq_mul_inv, ←Rat.div_eq_mul_inv]
    rw [←Rat.mul_one 1]
    apply Rat.mul_lt_mul_of_pos
    · apply Rat.abs_pos
      have : A ≠ 0 := by symm; apply ne_of_lt; assumption
      invert_tactic
    · apply (Rat.abs_div_lt_one _ _ _).mpr
      rw [Rat.abs_of_pos, Rat.abs_of_pos]
      apply lt_of_lt_of_le _ A_le_an
      apply Rat.half_lt
      assumption
      apply lt_of_lt_of_le A_pos A_le_an
      apply Rat.half_pos
      assumption
    · apply Rat.abs_pos
      have : B ≠ 0 := by symm; apply ne_of_lt; assumption
      invert_tactic
    · apply (Rat.abs_div_lt_one _ _ _).mpr
      rw [Rat.abs_of_pos, Rat.abs_of_pos]
      apply lt_of_lt_of_le _ B_le_bm
      apply Rat.half_lt
      assumption
      apply lt_of_lt_of_le B_pos B_le_bm
      apply Rat.half_pos
      assumption
  · apply Rat.mul_pos <;> apply Rat.half_pos <;> assumption

def CauchySeq.inv.spec (a b: CauchySeq) (ha: ¬a ≈ 0) : a ≈ b ->
  is_cauchy_equiv (fun n => if h:a n = 0 then 0 else (a n)⁻¹) (fun n => if h:b n = 0 then 0 else (b n)⁻¹) := by
  intro ab ε ε_pos
  simp
  rcases pos_or_neg_of_abs_pos (abs_pos_of_non_zero ha) with apos | aneg
  apply inv.spec_pos
  assumption
  assumption
  assumption
  have ⟨δ, prf⟩: Eventually₂ fun n m => ‖(if h : (-a).seq n = 0 then 0 else ((-a).seq n)⁻¹) - if h : (-b).seq m = 0 then 0 else ((-b).seq m)⁻¹‖ < ε := by
    apply inv.spec_pos
    assumption
    apply Quotient.exact
    show -⟦a⟧ = -⟦b⟧
    congr 1
    exact Quotient.sound ab
    assumption
  refine ⟨δ, ?_⟩
  intro n m δn δm
  replace prf := prf n m δn δm
  simp at prf
  apply lt_of_le_of_lt _ prf
  clear prf
  rw [←Rat.abs_neg]
  apply le_of_eq
  congr
  split <;> split
  · rw [dif_pos, dif_pos]
    rfl
    rename_i h
    rw [h]; rfl
    rename_i h _
    rw [h]; rfl
  · rw [dif_pos, dif_neg]
    rw [Rat.sub_eq_add_neg, Rat.neg_inv, Rat.neg_add, Rat.sub_eq_add_neg]
    rfl
    rename_i h
    intro g; apply h
    rw [←Rat.neg_neg (b m), g]; rfl
    rename_i h _
    rw [h]; rfl
  · rw [dif_neg, dif_pos]
    rw [Rat.sub_zero, Rat.sub_zero, Rat.neg_inv]
    rename_i h; rw [h]; rfl
    rename_i h _
    intro g; apply h
    rw [←Rat.neg_neg (a n), g]; rfl
  · rw [dif_neg, dif_neg]
    rw [Rat.neg_sub, ←Rat.neg_sub_neg, Rat.neg_inv, Rat.neg_inv]
    rename_i h
    intro g; apply h
    rw [←Rat.neg_neg (b m), g]; rfl
    rename_i h _
    intro g; apply h
    rw [←Rat.neg_neg (a n), g]; rfl

def CauchySeq.inv (a: CauchySeq) (ha: ¬a ≈ 0) : CauchySeq where
  seq n := if h:a n = 0 then 0 else (a n)⁻¹
  is_cacuhy := by
    apply CauchySeq.inv.spec
    assumption
    rfl

instance : CheckedInvert CauchySeq (fun x => ¬x ≈ 0) := ⟨.inv⟩

def Real.inv (a: ℝ) : a ≠ 0 -> ℝ := by
  apply a.hrecOn (motive := fun a => a ≠ (0: ℝ) -> ℝ)
  case f =>
    intro a eq
    refine ⟦a.inv ?_⟧
    intro g
    apply eq
    apply Quotient.sound
    assumption
  case c =>
    intro a b eqv
    apply Function.hfunext
    rw [Quotient.sound eqv]
    intro ha hb eq
    apply heq_of_eq
    apply Quotient.sound
    apply CauchySeq.inv.spec
    intro g
    apply ha
    apply Quotient.sound
    assumption
    assumption

instance : CheckedInvert ℝ (fun x => x ≠ 0) := ⟨.inv⟩

instance : CheckedDiv ℝ (fun x => x ≠ 0) where
  checked_div a b h := a * b⁻¹

instance : Min ℝ where
  min x y := (x + y - ‖x - y‖) /? 2
instance : Max ℝ where
  max x y := (x + y + ‖x - y‖) /? 2
