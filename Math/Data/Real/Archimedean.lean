import Math.Data.Real.OrderedAlgebra

def arch : ∀ (x : ℝ) {y : ℝ}, 0 < y → ∃ n : ℕ, x ≤ n • y := by
  intro x y ypos
  cases x, y with | mk x y =>
  have ⟨bound, bound_nonneg, bound_spec⟩ := x.upper_bound_with 0
  rw [Real.zero_lt_iff_pos] at ypos
  obtain ypos: y.IsPos := ypos
  obtain ⟨l, lpos, spec⟩ := ypos
  have lnz: l ≠ 0 := (ne_of_lt lpos).symm
  exists (bound /? l).ceil.natAbs
  apply CauchySeq.le_pointwise
  intro n
  show _ ≤ ((bound /? l).ceil.natAbs: ℚ) * _
  sorry

def exists_isLUB {S : Set ℝ} (hne : S.Nonempty) (hbdd : S.BoundedAbove) : ∃ x, S.IsLUB x := by
  sorry

instance : SupSet ℝ where
  sSup := sorry

def Real.ofIncreasingBounded
  (f: Nat -> ℝ)
  (inc: ∀n, f n ≤ f (n + 1))
  (bounded: ∃B, ∀n, f n ≤ B) : ℝ := by
  sorry
