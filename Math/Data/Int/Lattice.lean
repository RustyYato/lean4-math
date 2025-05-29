import Math.Data.Set.Order.Bounds
import Math.Order.Lattice.ConditionallyComplete
import Math.Data.Int.Order
import Math.Data.Nat.Find

noncomputable section

open scoped Classical

namespace Int

instance : Max Int where
  max := max
instance : Min Int where
  min := min

def exists_max_of_bounded_above (S: Set Int) (h: S.Nonempty) (hbdd: S.BoundedAbove) : ∃x: Int, x ∈ S ∧ ∀y ∈ S, y ≤ x := by
  classical
  obtain ⟨x, hx⟩ := h
  obtain ⟨ub, hub⟩ := hbdd
  have h : ∃n: Nat, ub - n ∈ S := ⟨(ub - x).toNat, ?_⟩
  let n := Nat.findP (P := fun n => ub - n ∈ S) h
  have lt_n: ∀m: Nat, m < n -> ub - m ∉ S := Nat.lt_findP_spec h
  exists ub - n
  apply And.intro (Nat.findP_spec h)
  intro y hy
  have : y ≤ ub := hub y hy
  have := Classical.contrapositive.mpr (lt_n (ub - y).toNat) ?_
  apply le_of_not_lt
  intro g; apply this
  clear this
  rw [←Int.ofNat_lt, Int.ofNat_toNat]
  omega
  rw [Classical.not_not]
  rw [Int.ofNat_toNat]
  rw [show ub - max (ub - y) 0 = y from ?_]
  assumption
  omega
  rw [Int.ofNat_toNat]
  rw [show ub - max (ub - x) 0 = x from ?_]
  assumption
  have : x ≤ ub := hub x hx
  omega

def exists_min_of_bounded_below (S: Set Int) (h: S.Nonempty) (hbdd: S.BoundedBelow) : ∃x: Int, x ∈ S ∧ ∀y ∈ S, x ≤ y := by
  have ⟨x, hx, xmax⟩ := exists_max_of_bounded_above (S.preimage (-·)) ?_ ?_
  exists -x
  apply And.intro hx
  intro y hy
  have := xmax (-y) (by
    rw [Set.mem_preimage, Int.neg_neg]
    assumption)
  omega
  obtain ⟨x, h⟩ := h
  exists -x
  rw [Set.mem_preimage, Int.neg_neg]
  assumption
  obtain ⟨x, hx⟩ := hbdd
  exists (-x)
  intro y hy
  rw [Set.mem_preimage] at hy
  have := hx _ hy
  omega

instance : SupSet Int where
  sSup S :=
    if h:S.Nonempty ∧ S.BoundedAbove then
      Classical.choose (exists_max_of_bounded_above _ h.left h.right)
    else
      0
instance : InfSet Int where
  sInf S :=
    if h:S.Nonempty ∧ S.BoundedBelow then
      Classical.choose (exists_min_of_bounded_below _ h.left h.right)
    else
      0

instance : IsConditionallyCompleteLattice Int where
  le_max_right := le_max_right
  le_max_left := le_max_left
  min_le_right := min_le_right
  min_le_left := min_le_left
  max_le := by
    intro a b k ak bk
    apply max_le_iff.mpr
    omega
  le_min := by
    intro a b k ak bk
    apply le_min_iff.mpr
    omega
  le_csSup := by
    intro S a h ha
    simp [sSup]
    rw [dif_pos ⟨⟨_, ha⟩, h⟩]
    have := Classical.choose_spec (exists_max_of_bounded_above S ⟨_, ha⟩ h)
    apply this.right
    assumption
  csSup_le := by
    intro S a h ha
    simp [sSup]
    rw [dif_pos ⟨h, ⟨_, ha⟩⟩]
    have := Classical.choose_spec (exists_max_of_bounded_above S h ⟨_, ha⟩)
    apply ha
    apply this.left
  csInf_le := by
    intro S a h ha
    simp [sInf]
    rw [dif_pos ⟨⟨_, ha⟩, h⟩]
    have := Classical.choose_spec (exists_min_of_bounded_below S ⟨_, ha⟩ h)
    apply this.right
    assumption
  le_csInf := by
    intro S a h ha
    simp [sInf]
    rw [dif_pos ⟨h, ⟨_, ha⟩⟩]
    have := Classical.choose_spec (exists_min_of_bounded_below S h ⟨_, ha⟩)
    apply ha
    apply this.left

end Int

end
