import Math.Order.Lattice.ConditionallyComplete
import Math.Data.Real.Div
import Math.Data.Real.Archimedean
import Math.Data.Int.Lattice

noncomputable section

open Classical Real

instance : Sup ℝ where
  sup := max
instance : Inf ℝ where
  inf := min

instance : NeZero (2: ℝ) where
  out := by
    intro h
    have ⟨k, spec⟩ := Quotient.exact h (1 /? 2) (by decide)
    replace spec := spec _ _ (le_refl _) (le_refl _)
    contradiction

def exists_isLUB {S : Set ℝ} (hne : S.Nonempty) (hbdd : S.BoundedAbove) : ∃ x, S.IsLUB x := by
  classical
  obtain ⟨L, hL⟩ := hne
  obtain ⟨U, hU⟩ := hbdd
  let S' (d: ℕ) := (Set.mk fun m: ℤ => ∃ y ∈ S, (m : ℝ) ≤ y * d)
  have : ∀ d : ℕ, Set.BoundedAbove (S' d) := by
    sorry
  let f := fun d => sSup (S' d)
  have hf₁ : ∀n (hn: 0 < n), ∃ y ∈ S, ((f n /? n ~(by
    intro h
    sorry): ℚ) : ℝ) ≤ y := by
    intro n hn
    sorry
  -- have := by
  --   intro S a h ha
  --   simp [sSup]
  --   rw [dif_pos ⟨⟨_, ha⟩, h⟩]
  --   have := Classical.choose_spec (exists_max_of_bounded_above S ⟨_, ha⟩ h)
  --   apply this.right
  --   assumption
  -- cases L, U with | mk L U =>
  -- exists ⟦{
  --   seq n := Rat.binarySearch (fun x => x ∈ S.upperBounds) (L n) (U n) n
  --   is_cacuhy := (by
  --     sorry)
  -- }⟧
  -- apply And.intro
  -- intro x hx



  sorry

instance : SupSet ℝ where
  sSup := sorry

-- this needs exists_isLUB, which requires proving that the reals
-- are an Archemedian set

-- instance : SupSet ℝ where
--   sSup S := if h:S.upperBounds.BoundedBelow then
--     Classical.choose h else 0
-- instance : InfSet ℝ where
--   sInf S := if h:S.lowerBounds.BoundedAbove then Classical.choose h else 0

-- instance : IsConditionallyCompleteLattice ℝ where
--   le_sup_left := le_max_left
--   le_sup_right := le_max_right
--   inf_le_left := min_le_left
--   inf_le_right := min_le_right
--   sup_le := by
--     intro a b k ak bk
--     apply max_le_iff.mpr
--     apply And.intro <;> assumption
--   le_inf := by
--     intro a b k ka kb
--     apply le_min_iff.mpr
--     apply And.intro <;> assumption
--   le_csSup := by
--     intro s a b x
--     simp [sSup]
--     obtain ⟨r, mem_upperbounds⟩ := b
--     have : s.upperBounds.BoundedBelow := by
--       exists a
--       intro b hb
--       apply hb
--       assumption
--     rw [dif_pos this]
--     have this := Classical.choose_spec this
--     rw [Set.mem_lowerBounds] at this

--     sorry
--   csSup_le := sorry
--   le_csInf := sorry
--   csInf_le := sorry

end
