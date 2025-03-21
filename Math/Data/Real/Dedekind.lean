import Math.Data.Real.CeilFloor
import Math.Data.Set.Order.Bounds
import Math.Algebra.Ring.Char

noncomputable section

open Real Classical

@[ext]
structure DedekindCut where
  lower: Set ℚ
  lower_nonempty: lower.Nonempty
  not_univ: ∃x, x ∉ lower
  lower_no_max: ∀x ∈ lower, ∃y ∈ lower, x < y
  lower_closed_down: ∀x ∈ lower, ∀y ≤ x, y ∈ lower

namespace DedekindCut

def upper (c: DedekindCut) : Set ℚ := c.lowerᶜ
def upper_closed_up (c: DedekindCut) : ∀x ∈ c.upper, ∀y, x ≤ y -> y ∈ c.upper := by
  intro x hx y hy m
  have := c.lower_closed_down y m x hy
  contradiction
def upper_nonempty (c: DedekindCut) : c.upper.Nonempty := c.not_univ

def upper_eq_lower_upperbounds (c: DedekindCut) : c.upper = c.lower.upperBounds := by
  ext x
  apply Iff.intro
  intro hx y hy
  apply le_of_not_lt
  intro h
  have := c.lower_closed_down y hy x (le_of_lt h)
  contradiction
  intro h g
  have ⟨y, hy, xlty⟩  := c.lower_no_max x g
  have := not_lt_of_le (h y hy)
  contradiction

def lower_lt_upper (c: DedekindCut) (a b: ℚ) (ha: a ∈ c.lower) (hb: b ∈ c.upper) : a < b := by
  apply lt_of_le_of_not_le
  rw [upper_eq_lower_upperbounds] at hb
  exact hb _ ha
  intro h
  have := c.lower_closed_down _ ha _ h
  contradiction

-- a monotonically increasing sequence which is contained in lower
def seq₂ (c: DedekindCut) (a b: ℚ) : ℕ -> ℚ × ℚ
| 0 => (a, b)
| n + 1 =>
  let k := midpoint a b
  if k ∈ c.lower then
    c.seq₂ k b n
  else
    c.seq₂ a k n

def seq₂_fst_mem_lower (c: DedekindCut) (a b: ℚ) (ha: a ∈ c.lower) : ∀n, (c.seq₂ a b n).fst ∈ c.lower := by
  intro n
  induction n generalizing a b with
  | zero => assumption
  | succ n ih =>
    unfold seq₂
    dsimp; split
    apply ih
    assumption
    apply ih
    assumption

def seq₂_snd_mem_upper (c: DedekindCut) (a b: ℚ) (ha: b ∈ c.upper) : ∀n, (c.seq₂ a b n).snd ∈ c.upper := by
  intro n
  induction n generalizing a b with
  | zero => assumption
  | succ n ih =>
    unfold seq₂
    dsimp; split
    apply ih
    assumption
    apply ih
    assumption

def seq₂_fst_monotone (c: DedekindCut) (a b: ℚ) (h: a ≤ b) : Monotone (fun n => (c.seq₂ a b n).fst) := by
  intro n m g
  dsimp
  induction n generalizing m a b with
  | zero =>
    rw [seq₂]; clear g
    induction m generalizing a b with
    | zero => rfl
    | succ m ih =>
      unfold seq₂
      dsimp
      split
      apply flip le_trans
      apply ih
      apply le_trans
      apply midpoint_le_max
      apply max_le <;> trivial
      apply flip le_trans
      apply min_le_midpoint
      apply le_min <;> trivial
      apply ih
      apply flip le_trans
      apply min_le_midpoint
      apply le_min <;> trivial
  | succ n ih =>
    cases m with
    | zero => contradiction
    | succ m =>
      unfold seq₂
      dsimp
      split
      apply ih
      apply le_trans
      apply midpoint_le_max
      apply max_le <;> trivial
      apply Nat.le_of_succ_le_succ
      assumption
      apply ih
      apply flip le_trans
      apply min_le_midpoint
      apply le_min <;> trivial
      apply Nat.le_of_succ_le_succ
      assumption

def seq₂_snd_antitone (c: DedekindCut) (a b: ℚ) (h: a ≤ b) : Antitone (fun n => (c.seq₂ a b n).snd) := by
  intro n m g
  dsimp
  show (c.seq₂ a b m).snd ≤ (c.seq₂ a b n).snd
  induction n generalizing m a b with
  | zero =>
    rw [seq₂]; clear g; dsimp
    induction m generalizing a b with
    | zero => rfl
    | succ m ih =>
      unfold seq₂
      dsimp
      split
      apply ih
      apply le_trans
      apply midpoint_le_max
      apply max_le <;> trivial
      apply le_trans
      apply ih
      apply flip le_trans
      apply min_le_midpoint
      apply le_min <;> trivial
      apply le_trans
      apply midpoint_le_max
      apply max_le <;> trivial
  | succ n ih =>
    cases m with
    | zero => contradiction
    | succ m =>
      unfold seq₂
      dsimp
      split
      apply ih
      apply le_trans
      apply midpoint_le_max
      apply max_le <;> trivial
      apply Nat.le_of_succ_le_succ
      assumption
      apply ih
      apply flip le_trans
      apply min_le_midpoint
      apply le_min <;> trivial
      apply Nat.le_of_succ_le_succ
      assumption

def half_npow_pos (n: ℕ) : 0 < ((1: ℚ) /? 2) ^ n := by
  rw [div?_npow, one_npow]
  apply Rat.mul_pos
  apply zero_lt_one
  apply inv?_pos
  induction n with
  | zero => rw [npow_zero]; apply zero_lt_one
  | succ n ih =>
    rw [npow_succ]
    apply lt_of_lt_of_le
    assumption
    rw [mul_two]; rw (occs := [1]) [←add_zero (2 ^ n)]
    apply add_le_add_left
    apply le_of_lt; assumption

def seq₂_diff_bounds (c: DedekindCut) (a b: ℚ) (h: a ≤ b) (n: ℕ) : (c.seq₂ a b n).snd - (c.seq₂ a b n).fst = (1 /? 2) ^ n * (b - a) := by
  induction n generalizing a b with
  | zero =>
    rw [npow_zero]
    unfold seq₂
    simp
  | succ n ih =>
    unfold seq₂
    simp
    split <;> rename_i g
    · rw [ih]
      · rw [npow_succ, mul_assoc]
        congr
        unfold midpoint
        rw (occs := [1]) [←mul_div?_cancel (a := b) (b := 2)]
        rw [div?_eq_mul_inv?, ←mul_assoc, ←div?_eq_mul_inv?,
          sub_div?_sub₀, sub_eq_add_neg, neg_add_rev, two_mul, add_assoc,
          ←add_assoc _ (-b), add_neg_cancel, zero_add, ←sub_eq_add_neg]
        rw [mul_comm, div?_eq_mul_inv?, div?_eq_mul_inv?, one_mul]
      · apply le_trans
        apply midpoint_le_max
        apply le_of_eq; exact max_iff_le_left.mp h
    · rw [ih]
      · rw [npow_succ, mul_assoc]
        congr
        · unfold midpoint
          rw (occs := [2]) [←mul_div?_cancel (a := a) (b := 2)]
          rw [div?_eq_mul_inv? a, ←mul_assoc, ←div?_eq_mul_inv?,
            sub_div?_sub₀, sub_eq_add_neg, two_mul, neg_add_rev, add_comm a b, add_assoc,
            ←add_assoc _ (-a), add_neg_cancel, zero_add, ←sub_eq_add_neg]
          rw [mul_comm, div?_eq_mul_inv?, div?_eq_mul_inv?, one_mul]
      · apply flip le_trans
        apply min_le_midpoint
        apply le_of_eq; symm; exact min_iff_le_left.mp h

def seq₂_fst_lim (c: DedekindCut) (a b: ℚ) (ha: a ∈ c.lower) (hb: b ∈ c.upper) : ∀ε: ℚ, 0 < ε -> ∃n: ℕ, (c.seq₂ a b n).snd - (c.seq₂ a b n).fst < ε := by
  intro ε εpos
  let x := (b - a) /? ε
  let n := x.ceil
  exists ‖n‖
  have altb : a < b := lower_lt_upper c a b ha hb
  apply lt_of_le_of_lt
  rw [seq₂_diff_bounds c a b (le_of_lt altb) ‖n‖]
  clear ha hb c
  have ⟨ceil_pred_lt_x, x_le_ceil⟩ := (Rat.ceil_spec x x.ceil).mp rfl
  replace x_le_ceil : x ≤ n := x_le_ceil
  have := IsOrderedSemiring.mul_le_mul_of_nonneg_right _ _ x_le_ceil _ (le_of_lt εpos)
  unfold x at this
  rw [div?_mul_cancel] at this
  refine if hn:n = 0 then ?_ else ?_
  erw [hn, npow_zero, one_mul]
  erw [hn, zero_mul] at this
  apply lt_of_le_of_lt
  assumption
  assumption
  replace hn' : (‖n‖: ℚ) ≠ 0 := by
    intro g;
    rw [←natCast_zero] at g
    have := HasChar.natCast_inj g
    have := Int.natAbs_eq_zero.mp this
    contradiction
  replace := IsOrderedSemiring.mul_le_mul_of_nonneg_right _ _ this (1 /? ‖n‖) ?_
  rw [div?_eq_mul_inv?, one_mul, ←div?_eq_mul_inv?,
    mul_comm _ ε, mul_assoc] at this
  rw (occs := [2]) [←Int.sign_mul_natAbs n] at this
  erw [←intCast_mul, mul_assoc, intCast_ofNat, mul_inv?_cancel, mul_one] at this
  rcases Int.sign_trichotomy n with nsign | nsign | nsign
  · rw [nsign, intCast_one, mul_one] at this
    apply flip lt_of_lt_of_le
    assumption
    clear this x_le_ceil ceil_pred_lt_x
    rw [div?_npow, one_npow, div?_eq_mul_inv?, one_mul, mul_comm, div?_eq_mul_inv?]
    apply _root_.mul_lt_mul_of_pos_left
    · rw [inv?_lt_inv?]
      show _ < ((2: ℕ): ℚ) ^ _
      rw [←natCast_npow, Rat.natCast_lt_natCast]
      exact Nat.lt_two_pow_self
      show _ < ((2: ℕ): ℚ) ^ _
      rw [←natCast_npow, ←natCast_zero, Rat.natCast_lt_natCast]
      exact Nat.two_pow_pos ‖n‖
      apply lt_of_le_of_ne
      exact max_iff_le_left.mpr rfl
      symm; assumption
    refine Rat.add_lt_iff_lt_sub.mp ?_
    rwa [zero_add]
  · rw [Int.sign_eq_zero_iff_zero] at nsign
    contradiction
  · rw [nsign] at this
    rw [Int.sign_eq_neg_one_iff_neg] at nsign
    rw [←intCast_neg, intCast_one, ←neg_mul_right, mul_one] at this
    replace this : (b - a) /? ‖n‖ < 0 := by
      apply lt_of_le_of_lt this
      refine Rat.neg_lt_neg_iff.mpr ?_
      rwa [neg_neg]
    replace this := _root_.mul_lt_mul_of_pos_right _ _ this ‖n‖ ?_
    rw [div?_mul_cancel, zero_mul, ←Rat.lt_add_iff_sub_lt, zero_add] at this
    have := lt_asymm this altb
    contradiction
    apply lt_of_le_of_ne
    exact max_iff_le_left.mpr rfl
    symm; assumption
  · apply le_of_lt
    rw [div?_eq_mul_inv?, one_mul]
    apply inv?_pos
    apply lt_of_le_of_ne
    exact max_iff_le_left.mpr rfl
    symm; assumption

def seq₂_fst_nomax (c: DedekindCut) (a b: ℚ) (ha: a ∈ c.lower) (hb: b ∈ c.upper) (n: ℕ) : ∃m, (c.seq₂ a b n).fst < (c.seq₂ a b m).fst := by
  let a' := (c.seq₂ a b n).fst
  have ha' : a' ∈ c.lower := by
    apply seq₂_fst_mem_lower
    assumption
  have ⟨x, hx, a_lt_x⟩ := c.lower_no_max a' ha'
  have ⟨m, spec⟩ := c.seq₂_fst_lim a b ha hb (x - a') ?_
  exists m
  show a' < _
  rw [Rat.neg_lt_neg_iff, neg_sub, neg_sub, ←Rat.add_lt_iff_lt_sub,
    add_comm, ←add_sub_assoc, add_comm, add_sub_assoc] at spec
  apply lt_of_le_of_lt _ spec
  rw (occs := [1]) [←add_zero a']
  apply add_le_add_left
  rw [←Rat.add_le_iff_le_sub, zero_add]
  apply le_of_lt
  apply lower_lt_upper
  assumption
  apply seq₂_snd_mem_upper
  assumption
  rw [←Rat.add_lt_iff_lt_sub, zero_add]
  assumption

def toReal' (c: DedekindCut) (a b: ℚ) (ha: a ∈ c.lower) (hb: b ∈ c.upper) : ℝ := Real.mk ({
  seq n := (c.seq₂ a b n).fst
  is_cacuhy := by
    show Rat.is_cauchy _
    intro ε εpos
    have ⟨δ, hδ⟩ := c.seq₂_fst_lim a b ha hb ε εpos
    apply CauchySeq.Eventually₂.wlog₀
    exists δ
    intro n m hn hm n_lt_m
    simp
    apply lt_of_le_of_lt _ hδ
    clear hδ εpos ε
    have : a < b := by exact lower_lt_upper c a b ha hb
    have : 0 < b - a := by
      refine Rat.add_lt_iff_lt_sub.mp ?_
      rwa [zero_add]
    rw [_root_.abs_sub_comm, Rat.abs_of_nonneg _ (by
        refine Rat.add_le_iff_le_sub.mp ?_
        rw [zero_add]
        apply seq₂_fst_monotone
        apply le_of_lt; assumption
        assumption)]
    rw [←Rat.le_add_iff_sub_le, add_comm, ←add_sub_assoc, ←Rat.add_le_iff_le_sub,
      add_comm]
    apply _root_.add_le_add
    apply seq₂_fst_monotone
    apply le_of_lt; assumption
    assumption
    apply flip le_trans
    apply seq₂_snd_antitone
    apply le_of_lt; assumption
    exact hm
    simp [Opposite.mk, Opposite.get]
    apply le_of_lt
    apply lower_lt_upper c
    exact seq₂_fst_mem_lower c a b ha m
    exact seq₂_snd_mem_upper c a b hb m
})

def toReal'_spec (c: DedekindCut) (a b: ℚ) (ha: a ∈ c.lower) (hb: b ∈ c.upper) : c.lower = Set.mk fun x: ℚ => x < c.toReal' a b ha hb := by
  ext x; simp
  apply flip Iff.intro
  · intro ⟨B, Bpos, k, h⟩
    have := lt_of_lt_of_le Bpos (h k (le_refl _))
    simp at this
    rw [←Rat.add_lt_iff_lt_sub, zero_add] at this
    apply c.lower_closed_down (c.seq₂ a b k).fst _ x _
    apply seq₂_fst_mem_lower
    assumption
    apply le_of_lt; assumption
  · intro hx
    rcases Or.symm (lt_or_le a x) with x_le_a | a_lt_x
    · apply lt_of_le_of_lt (Real.ofRat_le.mpr x_le_a)
      unfold toReal'
      clear hx x_le_a x
      have ⟨m, hm⟩ := c.seq₂_fst_nomax a b ha hb 0
      let x := (c.seq₂ a b m).fst
      replace hm : a < x := hm
      exists x - a
      apply And.intro
      rwa [←Rat.add_lt_iff_lt_sub, zero_add]
      simp
      show CauchySeq.Eventually fun n => x - a ≤ (c.seq₂ a b n).fst - a
      exists m
      intro n hn
      rw [sub_eq_add_neg, sub_eq_add_neg]
      apply add_le_add_right
      apply seq₂_fst_monotone
      apply le_of_lt; apply lower_lt_upper
      assumption
      assumption
      assumption
    · have ⟨y, hy, x_lt_y⟩ := c.lower_no_max x hx
      apply lt_of_lt_of_le
      apply Real.ofRat_lt.mpr
      assumption
      apply CauchySeq.le_eventually_pointwise
      simp
      show CauchySeq.Eventually fun n => y ≤ _
      clear x_lt_y a_lt_x hx x
      have ⟨x, hx, y_lt_x⟩ := c.lower_no_max y hy
      have ⟨n, hn⟩ := c.seq₂_fst_lim a b ha hb (x - y) (by rwa [←Rat.add_lt_iff_lt_sub, zero_add])
      have : a ≤ b := by
        apply le_of_lt
        exact lower_lt_upper c a b ha hb
      exists n
      intro m hm
      rw [←Rat.lt_add_iff_sub_lt, add_comm, ←add_sub_assoc, ←Rat.add_lt_iff_lt_sub, add_comm,
        Rat.lt_add_iff_sub_lt, add_sub_assoc] at hn
      apply flip le_trans
      apply seq₂_fst_monotone
      assumption
      assumption
      apply flip le_trans
      apply le_of_lt; assumption
      rw (occs := [1]) [←add_zero y]
      apply add_le_add_left
      rw [←Rat.add_le_iff_le_sub, zero_add]
      apply le_of_lt
      apply lower_lt_upper
      assumption
      exact seq₂_snd_mem_upper c a b hb n

def toReal (c: DedekindCut) : ℝ := c.toReal' (Classical.choose c.lower_nonempty) (Classical.choose c.upper_nonempty) (Classical.choose_spec c.lower_nonempty) (Classical.choose_spec c.upper_nonempty)
def toReal_spec (c: DedekindCut) : c.lower = Set.mk fun x: ℚ => x < c.toReal := by apply toReal'_spec

end DedekindCut

end
