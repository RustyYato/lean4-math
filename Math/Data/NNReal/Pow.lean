import Math.Data.NNReal.Topology
import Math.Data.Real.IVT

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
  intro x
  simp
  have ⟨y, hy⟩ := Real.has_root (· ^ n - embedReal x) ?_ ?_ ?_
  exists ⟨|y|, ?_⟩
  rw [Real.mem_nonneg]; apply abs_nonneg
  apply embedReal.inj
  show x.val = |y| ^ n
  rw [←abs_npow]
  rw [←sub_zero (y ^ n), ←hy,
    sub_sub, add_comm, add_sub_cancel',
    (Real.abs_of_nonneg _).mp]
  rfl
  apply x.property
  show Topology.IsContinuous<| (fun x: ℝ × ℝ => x.1 - x.2) ∘ (fun a => (a ^ n, x.val))
  apply Topology.IsContinuous.comp'
  apply Topology.IsContinuous.prod_mk
  apply continuous_npow
  repeat infer_instance
  simp
  exists 0
  cases n; contradiction
  rw [zero_npow_succ, zero_sub, ←Real.neg_le_neg_iff, neg_neg]
  apply x.property
  simp
  cases n; contradiction
  rename_i n
  classical
  obtain ⟨x, xnonneg⟩ := x
  let x' : ℝ≥0 := ⟨x, xnonneg⟩
  replace xnonneg : 0 ≤ x := xnonneg
  by_cases hx:x = 0
  · subst x
    exists 0
    simp [zero_npow_succ]
    rfl
  · have xpos : 0 < x := lt_of_le_of_ne xnonneg (Ne.symm hx)
    exists if h:x < 1 then 1 /? x else x
    show _ ≤ _ - x
    rw [Real.le_sub_iff_add_le, zero_add]
    simp
    split <;> rename_i h
    · rw [div?_eq_mul_inv?, mul_npow, inv?_npow, one_npow, one_mul]
      suffices x * x ^ (n+1) ≤ 1 by
        have := mul_le_mul_of_nonneg_right _ _ this (x^(n+1))⁻¹? ?_
        rwa [one_mul, mul_assoc, mul_inv?_cancel, mul_one] at this
        apply le_of_lt
        apply inv?_pos
        show 0 < x' ^ (n + 1)
        apply npow_pos
        assumption
      rw [←npow_succ']
      show x' ^ (n + 1 + 1) ≤ 1
      apply npow_le_one
      apply le_of_lt; assumption
    · rw (occs := [1]) [←one_mul x, npow_succ]
      apply mul_le_mul_of_nonneg_right
      show 1 ≤ x' ^ n
      apply one_le_npow
      rwa [not_lt] at h
      assumption

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
