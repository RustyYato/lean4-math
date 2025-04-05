import Math.Data.CauchySeq.Basic

namespace CauchySeq

variable
  [FieldOps γ] [LT γ] [LE γ] [Min γ] [Max γ]
  [IsField γ] [IsLinearLattice γ] [IsStrictOrderedSemiring γ]

open Norm.ofAbs

def pos_or_neg_of_abs_pos {f : CauchySeq γ} (hf : Pos ‖f‖) : Pos f ∨ Pos (-f) := by
  classical
  obtain ⟨B, B_pos, pos⟩ := hf
  replace ⟨δ, prf⟩ := pos.to₂_right.merge (f.is_cacuhy _ (half_pos B_pos))
  replace ⟨pos, f_eqv⟩ := prf _ _  (le_refl _) (le_refl _)
  replace pos: B ≤ |f δ| := pos
  clear f_eqv
  rw [abs_def] at pos
  split at pos <;> rename_i h
  · clear h
    left
    refine ⟨_, half_pos B_pos, δ, ?_⟩
    intro n δ_n
    apply le_trans _ <| sub_abs_self_sub (f δ) (f n)
    apply flip le_trans
    apply sub_le_sub
    assumption
    apply le_of_lt
    simp at prf
    exact (prf δ n (le_refl _) δ_n).right
    rw [sub_half]
  · clear h
    right
    refine ⟨_, half_pos B_pos, δ, ?_⟩
    intro n δ_n
    apply le_trans _ <| sub_abs_self_sub (-f δ) (-f n)
    rw [neg_sub_neg]
    apply flip le_trans
    apply sub_le_sub
    assumption
    apply le_of_lt
    simp at prf
    exact (prf n δ δ_n (le_refl _)).right
    rw [sub_half]

def not_neg_of_pos {f: CauchySeq γ} : f.Pos -> ¬(-f).Pos := by
  intro pos neg
  obtain ⟨A, A_pos, pos⟩ := pos
  obtain ⟨B, B_pos, neg⟩ := neg
  have ⟨δ, prf⟩ := pos.merge neg
  have ⟨pos, neg⟩ := prf _ (le_refl _)
  have : - - f δ ≤ - B := neg_le_neg_iff.mp neg
  rw [neg_neg] at this
  have A_le_neg_B := le_trans pos this
  have := lt_of_lt_of_le A_pos A_le_neg_B
  have : - - B < 0 := by rwa [←neg_zero, ←neg_lt_neg_iff]
  rw [neg_neg] at this
  exact lt_asymm B_pos this

protected def add_pos {a b: CauchySeq γ} : a.Pos -> b.Pos -> (a + b).Pos := by
  intro apos bpos
  obtain ⟨A, A_pos, apos⟩ := apos
  obtain ⟨B, B_pos, bpos⟩ := bpos
  refine ⟨A + B, ?_, ?_⟩
  rw [←add_zero 0]
  apply add_lt_add
  assumption
  assumption
  have ⟨δ, prf⟩ := apos.merge bpos
  exists δ
  intro n δn
  replace prf := prf _ δn
  obtain ⟨apos, bpos⟩ := prf
  apply add_le_add <;> assumption

protected def mul_pos {a b: CauchySeq γ} : a.Pos -> b.Pos -> (a * b).Pos := by
  intro apos bpos
  obtain ⟨A, A_pos, apos⟩ := apos
  obtain ⟨B, B_pos, bpos⟩ := bpos
  refine ⟨A * B, ?_, ?_⟩
  apply mul_pos
  assumption
  assumption
  have ⟨δ, prf⟩ := apos.merge bpos
  exists δ
  intro n δn
  replace prf := prf _ δn
  obtain ⟨apos, bpos⟩ := prf
  apply le_trans
  apply mul_le_mul_of_nonneg_right
  assumption
  apply le_of_lt; assumption
  apply _root_.mul_le_mul_of_nonneg_left
  assumption
  apply le_trans _ apos
  apply le_of_lt; assumption

end CauchySeq
