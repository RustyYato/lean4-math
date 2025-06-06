import Math.Order.Lattice.ConditionallyComplete
import Math.Data.Real.Order
import Math.Data.Int.Lattice
import Math.Data.Real.Dedekind

noncomputable section

open scoped Classical
open Real

def Real.exists_rat_lt (r: ℝ) : ∃q: ℚ, q < r := by
  induction r using Cauchy.ind with | ofSeq r =>
  have ⟨q, hq⟩ := (-r).upper_bound
  exists -q - 1
  rw [sub_eq_add_neg, ←neg_add_rev, add_comm, ←ratCast_neg, neg_lt_neg_iff, neg_neg]
  apply flip lt_of_le_of_lt
  show (q: ℝ) < (q + 1)
  rw (occs := [1]) [←add_zero (q: ℝ)]
  apply add_lt_add_left
  apply zero_lt_one
  apply (Cauchy.mk_le _ _).mpr
  apply CauchySeq.le_pointwise
  intro n
  apply le_of_lt
  apply hq

def Real.exists_rat_gt (r: ℝ) : ∃q: ℚ, r < q := by
  have ⟨q, hq⟩ := (-r).exists_rat_lt
  exists -q
  rwa [neg_lt_neg_iff, neg_neg] at hq

def exists_isLUB {S : Set ℝ} (hne : S.Nonempty) (hbdd : S.BoundedAbove) : ∃ x, S.IsLUB x := by
  let d : DedekindCut := {
    lower := Set.mk fun x => ∃r ∈ S, x < r
    lower_nonempty := by
      obtain ⟨r, r_in_s⟩ := hne
      have ⟨q, hq⟩ := r.exists_rat_lt
      exists q
      exists r
    lower_no_max := by
      intro x ⟨y, hy, x_lt_y⟩
      have ⟨z, x_lt_y, z_lt_y⟩ := Real.exists_rat_between x y x_lt_y
      exists z
      apply And.intro
      exists y
      apply Real.ofRat_lt.mp
      assumption
    not_univ := by
      obtain ⟨r, hr⟩ := hbdd
      have ⟨q, hq⟩ := r.exists_rat_gt
      exists q
      intro ⟨r', r'_in_S, hr'⟩
      have := hr r' r'_in_S
      have := lt_asymm (lt_of_lt_of_le hr' this)
      contradiction
    lower_closed_down := by
      intro x ⟨r, R_in_s, x_lt_r⟩ y y_le_x
      exists r
      apply And.intro
      assumption
      apply lt_of_le_of_lt
      apply ofRat_le.mpr
      assumption
      assumption
  }
  exists d.toReal
  apply flip And.intro
  · intro r hr
    apply le_ext
    intro q hq
    have ⟨r', r'ins, q_lt_r'⟩ : q ∈ d.lower := by rwa [d.toReal_spec]
    apply lt_of_lt_of_le
    assumption
    apply hr
    assumption
  · intro r hr
    apply le_ext
    intro q hq
    suffices q ∈ d.lower by rwa [d.toReal_spec] at this
    exists r

def exists_isGLB {S : Set ℝ} (hne : S.Nonempty) (hbdd : S.BoundedBelow) : ∃ x, S.IsGLB x := by
  have ⟨x, hx⟩ := exists_isLUB (S := S.preimage (-·)) ?_ ?_
  · exists -x
    apply And.intro
    intro r hr
    rw [neg_le_neg_iff, neg_neg]
    apply hx.left
    rwa [Set.mem_preimage, neg_neg]
    intro r hr
    rw [neg_le_neg_iff, neg_neg]
    apply hx.right
    intro a ha
    rw [neg_le_neg_iff, neg_neg]
    apply hr
    assumption
  · obtain ⟨r, hr⟩ := hne
    exists -r
    rwa [Set.mem_preimage, neg_neg]
  · obtain ⟨r, hr⟩ := hbdd
    exists -r
    intro a ha
    rw [neg_le_neg_iff, neg_neg]
    apply hr
    assumption

instance : SupSet ℝ where
  sSup S := if h:S.Nonempty ∧ S.BoundedAbove then Classical.choose (exists_isLUB h.left h.right) else 0
instance : InfSet ℝ where
  sInf S := if h:S.Nonempty ∧ S.BoundedBelow then Classical.choose (exists_isGLB h.left h.right) else 0

instance : IsConditionallyCompleteLattice ℝ where
  le_max_left := le_max_left
  le_max_right := le_max_right
  min_le_left := min_le_left
  min_le_right := min_le_right
  max_le := by
    intro a b k ak bk
    apply max_le_iff.mpr
    apply And.intro <;> assumption
  le_min := by
    intro a b k ka kb
    apply le_min_iff.mpr
    apply And.intro <;> assumption
  le_csSup := by
    intro S a hbdd ha
    simp [sSup]
    rw [dif_pos]
    have := Classical.choose_spec (exists_isLUB ⟨a, ha⟩ hbdd)
    apply this.left
    assumption
    exact ⟨⟨a, ha⟩, hbdd⟩
  csSup_le := by
    intro S a hne ha
    simp [sSup]
    rw [dif_pos]
    have := Classical.choose_spec (exists_isLUB hne ⟨a, ha⟩)
    apply this.right
    assumption
    exact ⟨hne, ⟨a, ha⟩⟩
  le_csInf := by
    intro S a hne ha
    simp [sInf]
    rw [dif_pos]
    have := Classical.choose_spec (exists_isGLB hne ⟨a, ha⟩)
    apply this.right
    assumption
    exact ⟨hne, ⟨a, ha⟩⟩
  csInf_le := by
    intro S a hbdd ha
    simp [sInf]
    rw [dif_pos]
    have := Classical.choose_spec (exists_isGLB ⟨a, ha⟩ hbdd)
    apply this.left
    assumption
    exact ⟨⟨a, ha⟩, hbdd⟩

end

namespace Real

def max_mul (a b c: ℝ) (hc: 0 ≤ c) : (a ⊔ b) * c = (a * c) ⊔ (b * c) := by
  open scoped Classical in
  rw [max_def, max_def]
  split <;> rename_i h
  rw [if_pos]
  apply mul_le_mul_of_nonneg_right <;> assumption
  rcases lt_or_eq_of_le hc with hc | hc
  rw [if_neg]
  intro g

  have := mul_le_mul_of_nonneg_right _ _ g _ (le_of_lt (inv?_pos _ hc))
  rw [mul_assoc, mul_assoc, mul_inv?_cancel, mul_one, mul_one] at this
  contradiction
  rw [←hc]
  simp

def min_mul (a b c: ℝ) (hc: 0 ≤ c) : (a ⊓ b) * c = (a * c) ⊓ (b * c) := by
  open scoped Classical in
  rw [min_def, min_def]
  split <;> rename_i h
  rw [if_pos]
  apply mul_le_mul_of_nonneg_right <;> assumption
  rcases lt_or_eq_of_le hc with hc | hc
  rw [if_neg]
  intro g
  have := mul_le_mul_of_nonneg_right _ _ g _ (le_of_lt (inv?_pos _ hc))
  rw [mul_assoc, mul_assoc, mul_inv?_cancel, mul_one, mul_one] at this
  contradiction
  rw [←hc]
  simp

end Real
