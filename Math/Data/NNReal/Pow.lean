import Math.Data.NNReal.Topology
import Math.Data.Real.IVT
import Math.AxiomBlame

namespace NNReal

-- def npowMono (n: ℕ) : Monotone (α := ℝ≥0) (· ^ n) := by
--   intro x y x_le_y
--   dsimp
--   cases n
--   contradiction
--   rename_i n
--   rw [npow_succ, npow_succ]
--   sorry

def npow_pos (x: ℝ≥0) (n: ℕ) : 0 < x -> 0 < x ^ n := by
  intro h
  induction n with
    | zero => rw [npow_zero]; apply zero_lt_one
    | succ n ih =>
      rw [npow_succ]
      apply mul_pos
      assumption
      assumption

def npow_le_one (x: ℝ≥0) (n: ℕ) : x ≤ 1 -> x ^ n ≤ 1 := by
  intro h
  induction n with
    | zero => rw [npow_zero]
    | succ n ih =>
      rw [npow_succ]
      rw [←mul_one 1]
      apply mul_le_mul
      assumption
      assumption

def one_le_npow (x: ℝ≥0) (n: ℕ) : 1 ≤ x -> 1 ≤ x ^ n := by
  intro h
  induction n with
    | zero => rw [npow_zero]
    | succ n ih =>
      rw [npow_succ]
      rw [←mul_one 1]
      apply mul_le_mul
      assumption
      assumption

def npowStrictMono (n: ℕ) (h: 0 < n) : StrictMonotone (α := ℝ≥0) (· ^ n) := by
  intro x y x_lt_y
  dsimp
  cases n
  contradiction
  rename_i n
  by_cases h:x = 0
  · subst h
    clear h
    rw [zero_npow_succ]
    apply npow_pos
    assumption
  rw [npow_succ, npow_succ]
  apply lt_of_lt_of_le
  apply mul_lt_mul_of_pos_left (α := ℝ≥0)
  assumption
  apply npow_pos
  apply lt_of_le_of_ne
  apply bot_le
  symm; assumption
  apply mul_le_mul_of_nonneg_right _ _ _ _ (bot_le _)
  rename_i g; clear g
  induction n with
  | zero => rw [npow_zero, npow_zero]
  | succ n ih =>
    rw [npow_succ, npow_succ]
    apply mul_le_mul
    assumption
    apply le_of_lt
    assumption

def npowSurj (n: ℕ) (h: 0 < n) : Function.Surjective (α := ℝ≥0) (· ^ n) := by
  apply Topology.surjective
  continuity
  · apply Filter.tendsto_atTop_atTop_of_monotone
    refine StrictMonotone.toMonotone ?_
    exact npowStrictMono n h
    intro b
    classical
    refine if hb:b ≤ 1 then ?_ else ?_
    exists 1
    rwa [one_npow]
    exists b
    cases n
    contradiction
    rw (occs := [1]) [npow_succ, ←one_mul b]
    rename_i n; clear h
    apply mul_le_mul_right
    rw [←one_npow n]
    cases n
    rw [npow_zero, npow_zero]
    rename_i n
    apply (npowStrictMono _ (Nat.zero_lt_succ _)).le_iff_le.mpr
    apply le_of_not_le
    assumption
  · apply Filter.tendsto_atBot_atBot_of_monotone
    refine StrictMonotone.toMonotone ?_
    exact npowStrictMono n h
    intro b
    exists 0
    cases n; contradiction
    rw [zero_npow_succ]
    apply bot_le

noncomputable def npowOrderIso (n: ℕ) (h: 0 < n) : ℝ≥0 ≃o ℝ≥0 :=
  have := Equiv.ofBij (α := ℝ≥0) (f := (· ^ n)) ⟨(npowStrictMono n h).Injective, npowSurj n h⟩
  let eq := Classical.choose this
  let eq_spec := Classical.choose_spec this
  {
    toFun x := x ^ n
    invFun := eq.invFun
    leftInv := by rw [←eq_spec]; exact eq.leftInv
    rightInv := by rw [←eq_spec]; exact eq.rightInv
    resp_rel := (npowStrictMono n h).le_iff_le.symm
  }

end NNReal
