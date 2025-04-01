import Math.Order.Lattice.ConditionallyComplete
import Math.Order.Linear

open Classical

instance : Max Nat := ⟨max⟩
instance : Min Nat := ⟨min⟩

noncomputable
instance : SupSet Nat where
  sSup S := if h:S.BoundedAbove then S.upperBounds.min (· < ·) h else 0

noncomputable
instance : InfSet Nat where
  sInf S :=
    if h:S.Nonempty then
      S.lowerBounds.upperBounds.min (· < ·) <| by
        obtain ⟨x, h⟩ := h
        exists x
        intro y hy
        apply hy
        assumption
    else
      0

instance : IsConditionallyCompleteLattice Nat where
  le_max_left := le_max_left
  le_max_right := le_max_right
  min_le_left := min_le_left
  min_le_right := min_le_right
  max_le := by
    intro a b k ak bk
    show max a b ≤ k
    rw [max_def]
    split <;> assumption
  le_min := by
    intro a b k ak bk
    show k ≤ min a b
    rw [min_def]
    split <;> assumption
  le_csSup := by
    intro s a h ha
    simp [sSup]
    rw [dif_pos h]
    apply Set.min_mem (· < ·) h
    assumption
  csSup_le := by
    intro S a hn h
    simp [sSup]
    rw [dif_pos ⟨_, h⟩, le_iff_not_lt]
    apply Set.not_lt_min (· < ·) ⟨_, h⟩ a h
  csInf_le := by
    intro S a h amem
    rw [le_iff_not_lt]
    simp only [sInf]
    split
    refine Set.not_lt_min (s := S.lowerBounds.upperBounds) (· < ·) ?_ a ?_
    intro x hx
    apply hx
    assumption
    apply Nat.not_lt_zero
  le_csInf := by
    intro S a hs x
    simp [sInf]
    rw [dif_pos hs]
    apply Set.min_mem (s := S.lowerBounds.upperBounds) (· < ·)
    assumption
