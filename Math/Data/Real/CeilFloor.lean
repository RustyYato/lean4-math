import Math.Data.Real.Archimedean
import Math.Data.Nat.Lattice
import Math.Data.Int.Lattice

noncomputable section

namespace Real

open Classical

@[norm_cast]
def intCast_le {a b: ℤ} :  a ≤ (b: ℝ) ↔ a ≤ b := by
  apply ofRat_le.trans
  apply Rat.intCast_le
@[norm_cast]
def intCast_lt {a b: ℤ} :  a < (b: ℝ) ↔ a < b := by
  apply ofRat_lt.trans
  apply Rat.intCast_lt

def exists_floor (r: ℝ) : ∃n: ℤ, n ≤ r ∧ r < n + 1 := by
  have ⟨n, hn⟩ := exists_nat_gt r
  have ⟨z, hz⟩ := exists_int_lt r
  have exists_sub_lt: (∃i: ℕ, ↑(n - i: ℤ) ≤ r) := ?_
  let i := Nat.findP exists_sub_lt
  exists n - i
  apply And.intro
  exact Nat.findP_spec exists_sub_lt
  · cases hi:i with
    | zero =>
      rw [natCast_zero, sub_zero]
      apply lt_of_lt_of_le hn
      rw [intCast_ofNat, ←natCast_succ]
      apply ofRat_le.mpr
      apply (Rat.ofInt_le _ _).mp
      apply Int.ofNat_le.mpr
      apply Nat.le_succ
    | succ i₀ =>
    have := Nat.lt_findP_spec exists_sub_lt i₀
    conv at this => { intro m; rw [not_le] }
    apply lt_of_lt_of_le
    apply this
    show i₀ < i
    rw [hi]
    exact Nat.lt_add_one i₀
    norm_cast
    rw [natCast_succ]
    rw [sub_eq_add_neg, sub_eq_add_neg,
      neg_add_rev, add_comm (-1), add_assoc,
      add_assoc, neg_add_cancel, add_zero]
  exists (n - z).toNat
  rw [Int.ofNat_toNat, Int.max_eq_left, sub_sub, add_sub_assoc, add_sub_cancel]
  apply le_of_lt
  assumption
  refine Int.sub_nonneg_of_le ?_
  apply (Rat.ofInt_le _ _).mpr
  apply ofRat_le.mp
  apply le_of_lt
  apply lt_trans
  assumption
  assumption

def floor (r: ℝ) := Classical.choose r.exists_floor
def ceil (r: ℝ) := -(-r).floor

def floor_spec (r: ℝ) (x: Int) : r.floor = x ↔ x ≤ r ∧ r < x + 1 := by
  apply Iff.intro
  intro h
  subst h
  apply Classical.choose_spec r.exists_floor
  intro h
  have g : r.floor ≤ r ∧ r < r.floor + 1 := Classical.choose_spec r.exists_floor
  apply le_antisymm
  · apply Int.le_of_lt_add_one
    apply Rat.intCast_lt.mp
    apply ofRat_lt.mp
    apply lt_of_le_of_lt
    exact g.left
    rw [←intCast_add]
    exact h.right
  · apply Int.le_of_lt_add_one
    apply Rat.intCast_lt.mp
    apply ofRat_lt.mp
    apply lt_of_le_of_lt
    exact h.left
    rw [←intCast_add]
    exact g.right
def ceil_spec (a: ℝ) (x: Int) : a.ceil = x ↔ x - 1 < a ∧ a ≤ x := by
  unfold ceil
  rw (occs := [1]) [←neg_neg x]
  rw [neg_inj, floor_spec, ←intCast_neg, neg_le_neg_iff]
  norm_cast
  rw [←neg_neg ((-x + 1: ℤ): ℝ), intCast_neg,
    neg_add_rev, neg_neg, add_comm _ x, ←sub_eq_add_neg,
    neg_lt_neg_iff]
  apply And.comm
def ceil_eq_neg_floor_neg (a: ℝ) : a.ceil = -(-a).floor := rfl
def floor_eq_neg_ceil_neg (a: ℝ) : a.floor = -(-a).ceil := by
  rw [ceil_eq_neg_floor_neg, neg_neg, neg_neg]

attribute [irreducible] floor ceil

def floor_le_self (a: ℝ) : a.floor ≤ a := ((floor_spec a a.floor).mp rfl).left
def self_le_ceil (a: ℝ) : a ≤ a.ceil := ((ceil_spec a a.ceil).mp rfl).right
def floor_le (a: ℝ) : ∀x: ℤ, a ≤ x -> a.floor ≤ x := by
  intro x hx
  have := le_trans ((floor_spec a a.floor).mp rfl).left hx
  rw [intCast_le] at this
  assumption
def le_ceil (a: ℝ) : ∀x: ℤ, x ≤ a -> x ≤ a.ceil := by
  intro x hx
  have := le_trans hx ((ceil_spec a a.ceil).mp rfl).right
  rw [intCast_le] at this
  assumption
def of_floor_lt (a: ℝ) : ∀x: ℤ, a.floor < x -> a < x := by
  intro x hx
  have := ((floor_spec a a.floor).mp rfl).right
  rw [←intCast_one, intCast_add] at this
  apply lt_of_lt_of_le this
  rw [intCast_le, Int.add_one_le_iff]
  assumption
def of_lt_ceil (a: ℝ) : ∀x: ℤ, x < a.ceil -> x < a := by
  intro x hx
  rw [ceil_eq_neg_floor_neg,
    ←neg_neg x, Int.neg_lt_neg_iff] at hx
  have := of_floor_lt _ _ hx
  rw [←intCast_neg, neg_lt_neg_iff] at this
  assumption
def of_le_floor (a: ℝ) : ∀x: ℤ, x ≤ a.floor -> x ≤ a := by
  intro x h
  rw [←intCast_le] at h
  apply le_trans h
  apply floor_le_self
def of_ceil_le (a: ℝ) : ∀x: ℤ, a.ceil ≤ x -> a ≤ x := by
  intro x h
  rw [←intCast_le] at h
  apply le_trans _ h
  apply self_le_ceil
def of_lt_floor (a: ℝ) : ∀x: ℤ, x < a.floor -> x < a := by
  intro x h
  rw [←intCast_lt] at h
  apply lt_of_lt_of_le h
  apply floor_le_self
def of_ceil_lt (a: ℝ) : ∀x: ℤ, a.ceil < x -> a < x := by
  intro x h
  rw [←intCast_lt] at h
  apply lt_of_le_of_lt _ h
  apply self_le_ceil
def ceil_lt (a: ℝ) : ∀x: ℤ, x ≤ a -> x ≤ a.ceil := by
  intro x hx
  have := le_trans hx ((ceil_spec a a.ceil).mp rfl).right
  rw [intCast_le] at this
  assumption
def fract (a: ℝ) : ℝ := a - a.floor
def floor_add_fract (a: ℝ) : a.floor + a.fract = a := add_sub_cancel _ _
def sub_fract (a: ℝ) : a - a.fract = a.floor := by
  unfold fract
  rw [sub_sub, add_sub_assoc, add_sub_cancel]
def fract_spec (a: ℝ) : 0 ≤ a.fract ∧ a.fract < 1 := by
  unfold fract
  rw [le_sub_iff_add_le, zero_add, sub_lt_iff_lt_add, add_comm]
  apply (floor_spec _ _).mp
  rfl

def le_floor_of_lt_ceil (a: ℝ) : ∀x: ℤ, x < a.ceil -> x ≤ a.floor := by
  intro x h
  have := of_lt_ceil _ _ h
  have :=  lt_trans this ((floor_spec a a.floor).mp rfl).right
  rw [←intCast_succ, intCast_lt] at this
  apply Int.le_of_lt_add_one
  assumption

@[simp]
def intCast_floor (a: ℤ) : floor a = a := by
  apply (floor_spec _ _).mpr
  rw [←intCast_succ, intCast_le, intCast_lt]
  omega

@[simp]
def intCast_ceil (a: ℤ) : ceil a = a := by
  apply (ceil_spec _ _).mpr
  rw [←intCast_pred, intCast_le, intCast_lt]
  omega

def le_floor (a: ℝ) : ∀x: ℤ, x ≤ a.floor ↔ x ≤ a := by
  intro x
  apply Iff.intro
  apply of_le_floor
  intro h
  rcases lt_or_eq_of_le (le_ceil _ _ h) with h | h
  apply le_floor_of_lt_ceil; assumption
  subst x
  have := le_antisymm h (self_le_ceil _)
  rw [←this]
  simp
def ceil_le (a: ℝ) : ∀x: ℤ, a.ceil ≤ x ↔ a ≤ x := by
  intro x
  rw [ceil_eq_neg_floor_neg, ←Int.neg_le_neg_iff, neg_neg]
  rw [le_floor, ←intCast_neg, neg_le_neg_iff]

end Real

end
