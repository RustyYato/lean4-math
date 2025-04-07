import Math.Data.Real.MetricSpace

open Norm.ofAbs

example : ∀c: Cauchy ℝ, ∃r: ℝ, c = .of r := by
  intro c
  induction c with | ofSeq c =>
  let S : Set ℝ := Set.mk fun r => CauchySeq.const r < c
  have lb : ∃r, r ∈ S := by
    sorry
  -- have ub' : ∀ x, c < CauchySeq.const x → ∀ y ∈ S, y ≤ x := by
  --   intro r hr y hy
  --   obtain ⟨A, Apos, hr⟩ := hr
  --   obtain ⟨B, Bpos, hy⟩ := hy
  --   have ⟨δ, h⟩ := hr.merge hy
  --   replace h : (A ≤ r - c δ) ∧ (B ≤ c δ - y) := h δ (le_refl _)
  --   obtain ⟨hr, hy⟩ := h
  --   replace hr := le_trans (le_of_lt Apos) hr
  --   replace hy := le_trans (le_of_lt Bpos) hy
  --   have := add_nonneg _ _ hr hy
  --   rwa [←add_sub_assoc, sub_add_cancel, le_sub_iff_add_le, zero_add] at this
  have ub : ∃ x, ∀ y ∈ S, y ≤ x := sorry
  sorry
  -- exists (⨆ S)
  -- apply Relation.eq_of_not_lt_or_gt (· < ·)
  -- · intro ⟨B, Bpos, δ, h⟩
  --   replace h : ∀n, δ ≤ n -> B ≤ (⨆ S) - c n := h
  --   have := csSup_le lb (ub' ((⨆ S) - B /? 2) ?_)
  --   · rw [←not_lt] at this; apply this; clear this
  --     rw (occs := [1]) [sub_lt_iff_lt_add, ←add_zero (⨆ S)]
  --     apply add_lt_add_left
  --     apply half_pos
  --     assumption
  --   · exists B /? 2
  --     apply And.intro
  --     apply half_pos
  --     assumption
  --     exists δ
  --     intro n hn
  --     show _ ≤ (⨆ S) - B /? 2 - c n
  --     rw [←sub_add, add_comm, sub_add, le_sub_iff_add_le, add_half]
  --     apply h
  --     assumption
  -- · intro ⟨B, Bpos, δ, h⟩
  --   replace h : ∀n, δ ≤ n -> B ≤ c n - (⨆ S) := h
  --   have := le_csSup ub (a := (⨆ S) + B /? 2) ?_
  --   · rw [←not_lt] at this; apply this; clear this
  --     rw (occs := [1]) [←add_zero (⨆ S)]
  --     apply add_lt_add_left
  --     apply half_pos
  --     assumption
  --   · refine ⟨_, half_pos Bpos, δ, ?_⟩
  --     intro n hn
  --     show _ ≤ c n - ((⨆ S) + _)
  --     rw [add_comm, sub_add, le_sub_iff_add_le, add_half]
  --     apply h
  --     assumption
