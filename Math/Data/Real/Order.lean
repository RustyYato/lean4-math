import Math.Data.Real.Basic
import Math.Data.CauchySeq.Completion.Order

namespace Real

instance : LT ℝ := inferInstanceAs (LT (Cauchy ℚ))
instance : LE ℝ := inferInstanceAs (LE (Cauchy ℚ))
instance : Min ℝ := inferInstanceAs (Min (Cauchy ℚ))
instance : Max ℝ := inferInstanceAs (Max (Cauchy ℚ))
instance : IsLinearLattice ℝ := inferInstanceAs (IsLinearLattice (Cauchy ℚ))
instance : IsStrictOrderedSemiring ℝ := inferInstanceAs (IsStrictOrderedSemiring (Cauchy ℚ))

@[norm_cast]
def ofRat_lt {a b: ℚ} : (a: ℝ) < b ↔ a < b := by
  apply Iff.intro
  · intro h
    obtain ⟨B, B_pos, k, spec⟩ := h
    have : B ≤ b - a := spec k (le_refl _)
    rw [←Rat.add_le_iff_le_sub] at this
    apply lt_of_lt_of_le _ this
    rw (occs := [1]) [←zero_add a]
    apply Rat.add_lt_add_right.mp
    assumption
  · intro h
    exists b - a
    apply And.intro
    rw [←Rat.add_lt_iff_lt_sub, zero_add]; assumption
    exists 0
    intro n _
    apply le_refl

@[norm_cast]
def ofRat_le {a b: ℚ} : (a: ℝ) ≤ b ↔ a ≤ b := by
  apply le_iff_of_lt_iff
  apply ofRat_lt

instance : Archimedean ℝ := archimedean_iff_nat_lt.mpr <| by
  intro x
  induction x using Cauchy.ind with | ofSeq x =>
  have ⟨ub, ub_spec⟩ := x.upper_bound
  have ⟨n, ub_lt_n⟩ := archimedean_iff_nat_lt.mp (inferInstanceAs (Archimedean ℚ)) ub
  exists n
  apply flip lt_of_le_of_lt
  apply ofRat_lt.mpr
  assumption
  apply le_of_not_lt
  intro ⟨B, B_pos, k, spec⟩
  replace spec : B ≤ x k - ub := spec k (le_refl _)
  replace spec := lt_of_lt_of_le B_pos spec
  rw [←Rat.add_lt_iff_lt_sub, zero_add] at spec
  exact lt_asymm spec (ub_spec _)

def exists_nat_gt (r: ℝ) : ∃n: ℕ, r < n := by
  have ⟨n, spec⟩ := Archimedean.arch r (y := 1) zero_lt_one
  rw [←natCast_eq_nsmul_one] at spec
  exists n + 1
  rw [natCast_succ]
  apply lt_of_le_of_lt spec
  rw (occs := [1]) [←add_zero (n: ℝ)]
  rw [add_comm, add_lt_iff_lt_sub, add_comm, add_sub_cancel']
  apply zero_lt_one

def exists_int_lt (r: ℝ) : ∃n: ℤ, n < r := by
  rcases lt_or_le 0 r
  exists 0
  have ⟨n, spec⟩ := exists_nat_gt (-r)
  exists -n
  rw [←intCast_neg, intCast_ofNat, neg_lt_neg_iff, neg_neg]
  assumption

end Real
