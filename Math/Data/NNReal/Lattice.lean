import Math.Data.NNReal.Basic
import Math.Data.Real.Lattice

namespace NNReal

instance : Sup ℝ≥0 where
  sup := max
instance : Inf ℝ≥0 where
  inf := min

def nonempty_iff (S: Set ℝ≥0) : S.Nonempty ↔ (S.image orderEmbedReal).Nonempty := by
  apply Iff.intro
  intro ⟨x, hx⟩
  exists x.val
  apply Set.mem_image'
  assumption
  rintro ⟨_, ⟨x, hx, rfl⟩⟩
  refine ⟨x, ?_⟩
  assumption

def mem_upper_bounds_iff (S: Set ℝ≥0) (b: ℝ≥0) : b ∈ S.upperBounds ↔ b.val ∈ (S.image orderEmbedReal).upperBounds := by
  · apply flip Iff.intro
    · intro h a ha
      apply h
      apply Set.mem_image'
      assumption
    · rintro h _ ⟨x, hx, rfl⟩
      apply h
      assumption

def mem_lower_bounds_iff (S: Set ℝ≥0) (b: ℝ≥0) : b ∈ S.lowerBounds ↔ b.val ∈ (S.image orderEmbedReal).lowerBounds := by
  · apply flip Iff.intro
    · intro h a ha
      apply h
      apply Set.mem_image'
      assumption
    · rintro h _ ⟨x, hx, rfl⟩
      apply h
      assumption

def bdd_above_iff (S: Set ℝ≥0) : S.BoundedAbove ↔ (S.image orderEmbedReal).BoundedAbove := by
  by_cases h:S.Nonempty
  · obtain ⟨x, hx⟩ := h
    apply flip Iff.intro
    · intro ⟨b, hb⟩
      refine ⟨⟨b, ?_⟩, ?_⟩
      apply le_trans x.property
      apply hb
      apply Set.mem_image'
      assumption
      rwa [mem_upper_bounds_iff]
    · intro ⟨b, hb⟩
      exists b.val
      rwa [←mem_upper_bounds_iff]
  · rw [Set.not_nonempty _ h, Set.empty_image]
    apply Iff.intro
    intro
    exists 0
    intro _ _; contradiction
    intro
    exists 0
    intro _ _; contradiction

def zero_mem_lowerbounds (S: Set ℝ≥0) : 0 ∈ S.lowerBounds := by
  intro x hx
  apply x.property

def zero_mem_lowerbounds' (S: Set ℝ≥0) : 0 ∈ (S.image orderEmbedReal).lowerBounds := by
  rintro x ⟨x, _, rfl⟩
  apply x.property

def bdd_below (S: Set ℝ≥0) : S.BoundedBelow := by
  exists 0
  apply zero_mem_lowerbounds

noncomputable instance : SupSet ℝ≥0 where
  sSup S := ⟨sSup (S.image orderEmbedReal), by
    by_cases h:S.BoundedAbove ∧ S.Nonempty
    have ⟨x, hx⟩ := h.right
    apply le_trans x.property
    apply le_csSup
    rw [←bdd_above_iff]
    exact h.left
    apply Set.mem_image'
    assumption
    simp [sSup]; rw [dif_neg]
    rw [←nonempty_iff, ←bdd_above_iff]
    rwa [And.comm]⟩
noncomputable instance : InfSet ℝ≥0 where
  sInf S := ⟨sInf (S.image NNReal.orderEmbedReal), by
    by_cases h:S.Nonempty
    apply le_csInf
    rwa [←nonempty_iff]
    apply zero_mem_lowerbounds'
    simp [sInf]; rw [dif_neg]
    rw [←nonempty_iff]
    intro ⟨_, _⟩
    contradiction⟩

instance : IsConditionallyCompleteLattice ℝ≥0 where
  le_sup_left := le_max_left
  le_sup_right := le_max_right
  inf_le_left := min_le_left
  inf_le_right := min_le_right
  sup_le := by
    intro a b k ak bk
    apply max_le_iff.mpr
    apply And.intro <;> assumption
  le_inf := by
    intro a b k ka kb
    apply le_min_iff.mpr
    apply And.intro <;> assumption
  le_csSup := by
    intro S a hbdd ha
    apply le_csSup (α := ℝ)
    rwa [←bdd_above_iff]
    apply Set.mem_image'
    assumption
  csSup_le := by
    intro S a hne ha
    apply csSup_le (α := ℝ)
    rwa [←nonempty_iff]
    rwa [←mem_upper_bounds_iff]
  le_csInf := by
    intro S a hne ha
    apply le_csInf (α := ℝ)
    rwa [←nonempty_iff]
    rwa [←mem_lower_bounds_iff]
  csInf_le := by
    intro S a hbdd ha
    apply csInf_le (α := ℝ)
    exists 0
    apply zero_mem_lowerbounds'
    apply Set.mem_image'
    assumption

end NNReal
