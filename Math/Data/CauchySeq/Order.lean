import Math.Data.CauchySeq.Basic

namespace CauchySeq

variable
  [FieldOps γ] [LatticeOps γ]
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

def pos_or_eq_or_neg (a: CauchySeq γ) : a.Pos ∨ a ≈ 0 ∨ (-a).Pos := by
  by_cases h:a ≈ 0
  right; left; assumption
  cases pos_or_neg_of_abs_pos (f := a) (by
    have : (‖a‖ - 0).Pos := (norm_pos_of_not_zero _ h)
    rwa [sub_zero] at this)
  left; assumption
  right; right; assumption

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

def lt (a b: CauchySeq γ) : Prop := (b - a).Pos
def le : CauchySeq γ -> CauchySeq γ -> Prop := Relation.or_eqv (lt (γ := γ)) (· ≈ ·)

instance : Relation.IsTrans (lt (γ := γ)) where
  trans {a b c} h g := by
    obtain ⟨A, Apos, hA⟩ := h
    obtain ⟨B, Bpos, hB⟩ := g
    have ⟨δ, hδ⟩  := hA.merge hB
    simp at hδ
    exists A + B
    apply And.intro
    rw [←add_zero 0]; apply add_lt_add
    assumption; assumption
    exists δ
    intro n hn
    replace hδ := hδ n hn
    show A + B ≤ c n - a n
    rw [←add_zero (c n), ←neg_add_cancel (b n),
      ←add_assoc, add_sub_assoc, ←sub_eq_add_neg]
    rw [add_comm]; apply add_le_add
    exact hδ.right
    exact hδ.left

instance : Relation.IsIrrefl (lt (γ := γ)) where
  irrefl {a} := by
    show ¬Pos (a - a); simp
    intro h; exact non_zero_of_Pos _ h (by rfl)

instance : Relation.IsStrictLinearOrder (lt (γ := γ)) (· ≈ ·) where
  connected_by a b := by
    rcases pos_or_eq_or_neg (b - a) with h | h | h
    left; assumption
    right; left
    · intro ε εpos
      have ⟨δ, hδ⟩ := add.spec (b - a) a 0 a h (by rfl) ε εpos
      exists δ
      intro n m hn hm
      have : ‖((b m - a m) + a m) - (0 + a n)‖ < _ := hδ m n hm hn
      simp at this
      rwa [sub_add_cancel, norm_sub_comm] at this
    right; right; rwa [neg_sub] at h

instance : Relation.CongrEquiv (lt (γ := γ)) (· ≈ ·) where
  congr_eqv {a c b d} h g r := by
    show (d - c).Pos
    apply Pos.spec _ _ _ r
    apply sub.spec
    assumption
    assumption

instance : Relation.IsLawfulNonstrict le (lt (γ := γ)) (· ≈ ·) where
  is_lawful_nonstrict _ _ := Iff.rfl

instance : Relation.CongrEquiv (le (γ := γ)) (· ≈ ·) :=
  inferInstanceAs (Relation.CongrEquiv (Relation.or_eqv _ _) _)

instance : Relation.IsLinearOrder (le (γ := γ)) (· ≈ ·) :=
  inferInstanceAs (Relation.IsLinearOrder (Relation.or_eqv (lt (γ := γ)) (· ≈ ·)) (· ≈ ·))

end CauchySeq
