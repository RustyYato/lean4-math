import Math.Data.Real.CeilFloor
import Math.Data.Set.Order.Bounds

noncomputable section

open Real Classical

@[ext]
structure DedekindCut where
  lower: Set ℚ
  lower_nonempty: lower.Nonempty
  not_univ: ∃x, x ∉ lower
  lower_no_max: ∀x ∈ lower, ¬lower.IsGreatest x
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
  apply c.lower_no_max
  assumption
  apply And.intro
  assumption
  assumption

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

def seq₂_fst_antitone (c: DedekindCut) (a b: ℚ) (h: a ≤ b) : Antitone (fun n => (c.seq₂ a b n).snd) := by
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

def seq₂_fst_lim (c: DedekindCut) (a b: ℚ) (ha: a ∈ c.lower) (hb: b ∈ c.upper) :
  ∀ε: ℚ, 0 < ε -> ∃n: ℕ, (c.seq₂ a b n).snd - (c.seq₂ a b n).fst < ε := by
  intro ε εpos
  -- (b - a) /? ε < 2 ^ n
  sorry

def seq₂_fst_nomax (c: DedekindCut) (a b: ℚ) (ha: a ∈ c.lower) (hb: b ∈ c.upper) :
  ∀x ∈ c.lower, ∃n, x < (c.seq₂ a b n).fst := by
  intro q hq
  apply Classical.byContradiction
  intro hn
  rw [not_exists] at hn
  conv at hn => { intro; rw [not_lt] }
  replace hn := fun n => hn n


  -- intro x hx
  -- have a_lt_b : a < b := c.lower_lt_upper a b ha hb
  -- have fst_mem_lower := c.seq₂_fst_mem_lower a b ha
  -- have snd_mem_upper := c.seq₂_snd_mem_upper a b hb

  -- apply Classical.byContradiction
  -- intro hn
  -- rw [not_exists] at hn
  -- conv at hn => { intro; rw [not_lt] }
  -- replace hn := fun n => hn n



  sorry

def existsRealEqual (c: DedekindCut) : ∃r: ℝ, c.lower = Set.mk (fun x: ℚ => x < r) := by
  obtain ⟨l, hl⟩ := c.lower_nonempty
  obtain ⟨u, hu⟩ := c.upper_nonempty
  have is_cauchy : is_cauchy_equiv (c.seq l u) (c.seq l u) := ?_
  exists ⟦{
    seq := c.seq l u
    is_cacuhy := is_cauchy
  }⟧
  · ext x
    show x ∈ c.lower ↔ ∃B: ℚ, 0 < B ∧ CauchySeq.Eventually fun n => B ≤ c.seq l u n - x
    apply Iff.intro
    intro h




    repeat sorry
  · sorry

def toReal (c: DedekindCut) : ℝ := Classical.choose c.existsRealEqual
def toReal_spec (c: DedekindCut) : c.lower = Set.mk fun x: ℚ => x < c.toReal := Classical.choose_spec c.existsRealEqual

end DedekindCut

end
