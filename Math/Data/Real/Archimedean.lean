import Math.Data.Real.OrderedAlgebra
import Math.Data.Nat.Lattice
import Math.Algebra.Archimedean.Basic

namespace Real

instance : Archimedean ℝ := archimedean_iff_nat_lt.mpr <| by
  intro x
  induction x using ind with | mk x =>
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

def exists_isLUB {S : Set ℝ} (hne : S.Nonempty) (hbdd : S.BoundedAbove) : ∃ x, S.IsLUB x := by
  sorry

instance : SupSet ℝ where
  sSup := sorry

def Real.ofIncreasingBounded
  (f: Nat -> ℝ)
  (inc: ∀n, f n ≤ f (n + 1))
  (bounded: ∃B, ∀n, f n ≤ B) : ℝ := by
  sorry

end Real
