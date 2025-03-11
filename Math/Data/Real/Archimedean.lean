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

def exists_nat_gt (r: ℝ) : ∃n: ℕ, r < n := by
  have ⟨n, spec⟩ := Archimedean.arch r (y := 1) zero_lt_one
  rw [←natCast_eq_nsmul_one] at spec
  exists n + 1
  rw [natCast_succ]
  apply lt_of_le_of_lt spec
  rw (occs := [1]) [←add_zero (n: ℝ)]
  apply lt_iff_add_lt_add_left.mp
  apply zero_lt_one

def exists_int_lt (r: ℝ) : ∃n: ℤ, n < r := by
  rcases lt_or_le 0 r
  exists 0
  have ⟨n, spec⟩ := exists_nat_gt (-r)
  exists -n
  rw [←intCast_neg, intCast_ofNat, ←neg_lt_neg_iff, neg_neg]
  assumption

end Real
