import Math.Data.Real.Lattice
import Math.Order.GaloisConnection

namespace Real

def sqrt_set (r: ℝ) : Set ℝ := Set.mk fun x => x ^ 2 ≤ r
def mem_sqrt_set {r: ℝ} : ∀{x}, x ∈ r.sqrt_set ↔ x ^ 2 ≤ r := Iff.rfl

noncomputable def sqrt (r: ℝ) : ℝ := sSup r.sqrt_set

def neg_sq (r: ℝ) : (-r) ^ 2 = r ^ 2 := by
  rw [←neg_one_mul, mul_npow, npow_two, neg_one_mul, neg_neg, one_mul]

def abs_sq (r: ℝ) : ‖r‖ ^ 2 = r ^ 2 := by
  rw [abs_def]
  split
  rfl
  rw [neg_sq]

def sq_nonneg (r: ℝ) : 0 ≤ r ^ 2 := by
  rw [npow_two]
  rcases le_total 0 r with h | h
  apply mul_nonneg
  assumption
  assumption
  rw [←neg_neg (r * r), neg_mul_left, neg_mul_right]
  rw [←neg_le_neg_iff] at h
  apply mul_nonneg
  assumption
  assumption

def sqrt_set_bdd (r: ℝ) : r.sqrt_set.BoundedAbove := by
  exists max 1 r
  intro a ha
  rw [mem_sqrt_set] at ha
  rcases lt_or_le 1 a with h | h
  · rw [le_max_iff]; right
    apply flip le_trans
    assumption
    rw (occs := [1]) [←mul_one a, npow_two]
    apply mul_le_mul_of_nonneg_left
    apply le_of_lt; apply flip lt_trans
    assumption; exact zero_lt_one
    apply le_of_lt ;assumption
  · rw [le_max_iff]; left; assumption

def zero_mem_sqrt_set (r: ℝ) (h: 0 ≤ r) : 0 ∈ r.sqrt_set := by
  rw [mem_sqrt_set]
  assumption

def sqrt_set_nonempty (r: ℝ) (h: 0 ≤ r) : r.sqrt_set.Nonempty := by exists 0

def sq_sqrt (r: ℝ) : (r ^ 2).sqrt = ‖r‖ := by
  have hbdd : ‖r‖ ∈ (r ^ 2).sqrt_set.upperBounds := by
    intro a ha
    rw [mem_sqrt_set] at ha
    rcases Or.symm (lt_or_le ‖r‖ a) with h | h
    assumption
    suffices r ^ 2 < a ^ 2 by
      have := not_le_of_lt this
      contradiction
    clear ha
    rw [←abs_sq]
    rw [npow_two, npow_two]
    apply lt_of_le_of_lt
    apply mul_le_mul_of_nonneg_left
    exact IsLawfulAbs.abs_nonneg r
    apply le_of_lt; assumption
    apply mul_lt_mul_of_pos_right
    apply flip lt_of_le_of_lt
    assumption
    exact IsLawfulAbs.abs_nonneg r
    assumption
  apply le_antisymm
  · apply csSup_le
    · refine sqrt_set_nonempty (r ^ 2) ?_
      apply sq_nonneg
    · assumption
  · apply le_csSup
    exists ‖r‖
    rw [mem_sqrt_set, abs_sq]

def sqrt_nonneg (r: ℝ) (h: 0 ≤ r) : 0 ≤ r.sqrt := by
  apply le_csSup
  apply sqrt_set_bdd
  apply zero_mem_sqrt_set
  assumption

def sqrt_sq (r: ℝ) (h: 0 ≤ r) : r.sqrt ^ 2 = r := by
  apply le_antisymm
  · have : ∀x, 0 ≤ x -> x < r.sqrt -> x ^ 2 < r := by
      intro x xnonneg hx
      rw [←not_le] at *
      intro g; apply hx; clear hx
      apply csSup_le
      exact sqrt_set_nonempty r h
      intro a ha
      rw [mem_sqrt_set] at ha
      replace ha := le_trans ha g
      rcases Or.symm (lt_or_le 0 a) with h | h
      apply le_trans
      assumption
      assumption
      sorry
    sorry
  · apply le_of_not_lt
    intro g
    -- have : r.sqrt
    sorry


end Real

-- noncomputable def Real.sqrt : ℝ -> ℝ :=
--   Function.invFun_on (Set.mk fun x => 0 ≤ x) (fun a => a * a)

-- def Real.sqrt_of_sq_of_nonneg (a: ℝ) (h: 0 ≤ a): Real.sqrt (a * a) = a := by
--   apply Function.invFun_eq'_on (f := fun a: ℝ => a * a) _ h
--   intro a b ha hb eq
--   rw [Set.mk_mem] at ha hb
--   dsimp at eq
--   rcases lt_trichotomy a b with h | h | h
--   have := Real.mul_lt_mul_of_nonneg ha ha h h
--   rw [eq] at this; have := lt_irrefl this; contradiction
--   assumption
--   have := Real.mul_lt_mul_of_nonneg hb hb h h
--   rw [eq] at this; have := lt_irrefl this; contradiction

-- def Real.sqrt_of_sq (a: ℝ): Real.sqrt (a * a) = ‖a‖ := by
--   rw [abs_def]
--   split
--   rw [sqrt_of_sq_of_nonneg]
--   assumption
--   rw [←neg_neg (a * a), neg_mul_left, neg_mul_right, sqrt_of_sq_of_nonneg]
--   rw [←neg_le_neg_iff, neg_neg]
--   apply le_of_lt
--   apply lt_of_not_le
--   assumption

-- def Real.sq_sqrt (a: ℝ) (h: 0 ≤ a): Real.sqrt a * Real.sqrt a = a := by
--   apply Function.invFun_eq_on (f := fun a: ℝ => a * a)
--   exists a.sqrt
--   apply And.intro sorry
--   sorry

-- def Real.sqrt_surj (b: ℝ) (hb: 0 ≤ b) : ∃a, 0 ≤ a ∧ Real.sqrt a = b := by
--   exists b * b
--   apply And.intro
--   apply mul_nonneg <;> assumption
--   rw [sqrt_of_sq_of_nonneg _ hb]

-- def Real.sqrt_nonneg (a: ℝ) (ha: 0 ≤ a) : 0 ≤ a.sqrt := by
--   sorry

-- noncomputable def Real.sqrt_order_hom : { x: ℝ // 0 ≤ x } →o ℝ where
--   toFun x := Real.sqrt x
--   resp_rel := by
--     intro ⟨a, ha⟩ ⟨b, hb⟩ ab
--     dsimp
--     sorry

-- def Real.sq_surj (b: ℝ) (hb: 0 ≤ b) : ∃a, 0 ≤ a ∧ a * a = b := by
--   sorry

-- def Real.sqrt_inj (a b: ℝ) (ha: 0 ≤ a) (hb: 0 ≤ b) : Real.sqrt a = Real.sqrt b -> a = b := by
--   intro h
--   have : a.sqrt * a.sqrt = b.sqrt * b.sqrt := by rw [h]
--   rw [Real.sq_sqrt _ ha, Real.sq_sqrt _ hb] at this
--   assumption
