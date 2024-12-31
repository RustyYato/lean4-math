import Math.Logic.Basic

namespace Nat

def sqrt (n : Nat) : Nat :=
  if h:n ≤ 1 then n else
  let small := 2 * sqrt (n / 4)
  let large := small.succ
  if n < large*large then small else large
termination_by n
decreasing_by
  apply div_lt_self
  apply Nat.lt_of_not_le
  intro h
  cases Nat.le_zero.mp h
  contradiction
  trivial

def sqrt_sq_le_self (n: Nat): n.sqrt * n.sqrt ≤ n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
  cases Or.symm (Nat.lt_or_ge 1 n)
  · match n with
    | 0 =>
      unfold sqrt
      apply Nat.le_refl
    | 1 =>
      unfold sqrt
      apply Nat.le_refl
  · rename_i h
    unfold sqrt
    rw [dif_neg (Nat.not_le_of_lt h)]
    dsimp
    split
    suffices 2 * 2 * ((n / 4).sqrt * (n / 4).sqrt) ≤ n by
      apply Nat.le_trans _ this
      apply Nat.le_of_eq
      ac_rfl
    apply Nat.le_trans
    apply Nat.mul_le_mul
    apply Nat.le_refl
    apply ih
    apply Nat.div_lt_self
    apply Nat.zero_lt_of_lt
    assumption
    trivial
    apply Nat.mul_div_le
    apply Nat.le_of_not_lt
    assumption

def self_lt_sqrt_succ_sq (n: Nat): n < (n.sqrt + 1) * (n.sqrt + 1) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
  unfold sqrt
  split
  match n with
  | 0 | 1 => decide
  rename_i h
  simp
  split <;> rename_i g
  assumption
  replace g := Nat.le_of_not_lt g
  conv at g => { rhs; rw [←Nat.div_add_mod n 4] }
  conv => { lhs; rw [←Nat.div_add_mod n 4] }
  simp [Nat.add_mul, Nat.mul_add] at g
  have :
    2 * (n / 4).sqrt * (2 * (n / 4).sqrt) + 2 * (n / 4).sqrt + (2 * (n / 4).sqrt + 1) =
    4 * ((n / 4).sqrt * ((n / 4).sqrt)) + (2 * (n / 4).sqrt + 2 * (n / 4).sqrt) + 1 := by ac_rfl
  rw [this] at g; clear this
  rw [←Nat.two_mul, ←Nat.mul_assoc 2, ←Nat.mul_add] at g
  have : 1 + 1 = 2 := rfl
  rw [Nat.add_assoc, this]; clear this
  simp [Nat.add_mul, Nat.mul_add]
  have :
    2 * (n / 4).sqrt * (2 * (n / 4).sqrt) + 2 * (2 * (n / 4).sqrt) + (2 * (n / 4).sqrt * 2 + 4) =
    4 * ((n / 4).sqrt * (n / 4).sqrt) + 2 * 2 * (n / 4).sqrt + 4 + 2 * 2 * (n / 4).sqrt := by ac_rfl
  rw [this]; clear this
  rw [←Nat.mul_add, Nat.add_assoc]
  replace ih := ih (n / 4) (by
    refine div_lt_self ?_ ?_
    match n with
    | 0 => contradiction
    | n + 1 => apply Nat.zero_lt_succ
    decide)
  simp [Nat.add_mul, Nat.mul_add] at ih
  show _ < _ + (4 * 1 + 4 * _)
  rw [←Nat.mul_add 4, ←Nat.mul_add 4, Nat.add_comm 1]
  replace ih := Nat.mul_le_mul (Nat.le_refl 4) (Nat.succ_le_of_lt ih)
  rw [Nat.mul_succ] at ih
  replace ih := Nat.lt_of_succ_le ih
  apply Nat.lt_of_le_of_lt _ ih
  apply Nat.add_le_add_left
  apply Nat.le_of_lt_succ
  apply Nat.mod_lt
  decide

def div_le_div_const (a b k: Nat) : a ≤ b -> a / k ≤ b / k := by
  intro ab
  induction b, k using Nat.div.inductionOn generalizing a with
  | base b k h =>
    rw [Nat.div_eq b, if_neg h, Nat.div_eq a, if_neg]
    apply Nat.le_refl
    intro ⟨kpos, g⟩
    apply h
    apply And.intro kpos
    apply Nat.le_trans <;> assumption
  | ind b k h ih =>
    rw [Nat.div_eq b, if_pos h, Nat.div_eq]
    obtain ⟨kpos, h⟩ := h
    split
    apply Nat.succ_le_succ
    apply ih
    apply Nat.sub_le_iff_le_add.mpr
    rw [Nat.sub_add_cancel]
    assumption
    assumption
    rename_i g
    replace g := not_and.mp g kpos
    apply Nat.zero_le

def div_mul_le_mul_div (a b c d: Nat) : a / c * (b / d) ≤ (a * b) / (c * d) := by
  by_cases h:0 < c ∧ 0 < d
  apply (Nat.le_div_iff_mul_le _).mpr
  have : a / c * (b / d) * (c * d) = (c * (a / c)) * (d * (b / d)) := by ac_rfl
  rw [this]; clear this
  apply Nat.mul_le_mul
  apply Nat.mul_div_le
  apply Nat.mul_div_le
  apply Nat.mul_pos
  exact h.left
  exact h.right
  cases Decidable.not_and_iff_or_not.mp h
  all_goals
    rename_i h
    cases Nat.le_zero.mp (Nat.not_lt.mp h)
    rw [Nat.div_zero]
  rw [Nat.zero_mul]
  all_goals apply Nat.zero_le

def le_iff_sq_le (a b: Nat) : a ≤ b ↔ a * a ≤ b * b := by
  apply Iff.intro
  intro h
  apply Nat.le_trans
  apply Nat.mul_le_mul_left
  assumption
  apply Nat.mul_le_mul_right
  assumption
  intro h
  by_cases h:a ≤ b
  assumption
  cases b with
  | zero =>
    clear h
    cases Nat.mul_eq_zero.mp (Nat.le_zero.mp h)
    all_goals
      rename_i h
      rw [h]
      apply Nat.le_refl
  | succ b =>
  rename_i g
  have ba := Nat.lt_of_not_le h
  have : (b+1) * (b+1) < a * a := by
    apply Nat.lt_of_lt_of_le
    apply (Nat.mul_lt_mul_left _).mpr
    assumption
    apply Nat.zero_lt_succ
    apply Nat.mul_le_mul_right
    apply Nat.le_of_lt
    assumption
  have := Nat.lt_irrefl _ <| Nat.lt_of_lt_of_le this g
  contradiction

def lt_iff_sq_lt (a b: Nat) : a < b ↔ a * a < b * b := by
  apply Decidable.not_iff_not.mp
  apply Iff.trans Nat.not_lt
  apply Iff.trans _ Nat.not_lt.symm
  apply le_iff_sq_le

def sqrt_eq_iff (n x: Nat) : x = n.sqrt ↔ x * x ≤ n ∧ n < (x + 1) * (x + 1) := by
  apply Iff.intro
  intro h
  subst h
  apply And.intro
  apply sqrt_sq_le_self
  apply self_lt_sqrt_succ_sq
  revert x
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro x
  intro ⟨h, g⟩
  unfold sqrt
  split
  · match n with
    | 0 =>
      match x with
      | 0 => rfl
    | 1 =>
      match x with
      | 1 => rfl
  · dsimp
    rw [←Nat.div_add_mod x 2, ih (n/4) _ (x/2), Nat.mul_comm]
    have : (if n < ((n / 4).sqrt * 2 + 1) * ((n / 4).sqrt * 2 + 1) then (n / 4).sqrt * 2 else (n / 4).sqrt * 2 + 1)
      = (n / 4).sqrt * 2 + if n < ((n / 4).sqrt * 2 + 1) * ((n / 4).sqrt * 2 + 1) then 0 else 1 := by
        split <;> rfl
    rw [this]; clear this
    congr
    have rewrite : ∀x, x * x * (2*2) = (2 * x) * (2 * x) := by intro; ac_rfl
    split
    · rename_i oneltn n_lt
      have := sqrt_sq_le_self (n / 4)
      replace this := (le_div_iff_mul_le (by decide)).mp this
      replace this: (n / 4).sqrt * (n / 4).sqrt * (2 * 2) < _ := Nat.lt_of_le_of_lt this g
      rw [rewrite] at this; clear rewrite
      replace this := (lt_iff_sq_lt _ _).mpr this
      replace this := Nat.le_of_lt_succ this
      have le_x := this; clear this
      have := Nat.le_of_lt_succ <| (lt_iff_sq_lt _ _).mpr <| Nat.lt_of_le_of_lt h n_lt
      rw [Nat.mul_comm] at this
      cases Nat.le_antisymm le_x this
      rw [Nat.mul_mod_right]
    · rename_i oneltn le_n
      replace le_n := Nat.le_of_not_lt le_n
      have le_x := Nat.le_of_lt_succ <| (lt_iff_sq_lt _ _).mpr <| Nat.lt_of_le_of_lt le_n g
      have := self_lt_sqrt_succ_sq (n/4)
      replace this := (Nat.div_lt_iff_lt_mul (by decide)).mp this
      rw [rewrite] at this; clear rewrite
      replace this := Nat.lt_of_le_of_lt h this
      replace this := (lt_iff_sq_lt _ _).mpr this
      rw [Nat.mul_add, Nat.mul_comm] at this
      cases Nat.eq_of_le_of_lt_succ le_x this
      rw [Nat.add_mod, Nat.mul_mod_left]
    apply And.intro
    · apply Nat.le_trans _ (div_le_div_const (x*x) n 4 _)
      apply div_mul_le_mul_div
      assumption
    · apply Nat.div_lt_of_lt_mul
      apply Nat.lt_of_lt_of_le
      assumption
      show _ ≤ 2 * 2 * _
      have : 2 * 2 * ((x / 2 + 1) * (x / 2 + 1))
          = (2 * (x / 2 + 1)) * (2 * (x / 2 + 1)) := by ac_rfl
      rw [this]; clear this
      apply (le_iff_sq_le _ _).mp
      rw [Nat.mul_add, Nat.two_mul 1, ←Nat.add_assoc]
      conv => { lhs; rw [←Nat.div_add_mod x 2] }
      apply Nat.add_le_add_right
      apply Nat.add_le_add_left
      apply Nat.le_of_lt_succ
      apply Nat.mod_lt
      decide
    · refine div_lt_self ?_ ?_
      apply Nat.zero_lt_of_lt
      apply Nat.lt_of_not_le
      assumption
      decide

def le_sqrt_iff (n: Nat) : ∀{x}, x ≤ n.sqrt ↔ x * x ≤ n := by
  intro x
  have ⟨h ,g⟩  := (sqrt_eq_iff n _).mp rfl
  apply Iff.intro
  intro h'
  apply Nat.le_trans _ h
  apply Nat.mul_le_mul
  assumption
  assumption
  intro h'
  apply Nat.le_of_lt_succ
  apply (lt_iff_sq_lt _ _).mpr
  apply Nat.lt_of_le_of_lt h'
  assumption

def sqrt_lt_iff (n: Nat) : ∀{x}, sqrt n < x ↔ n < x * x := by
  intro x
  apply Decidable.not_iff_not.mp
  apply Iff.trans Nat.not_lt
  apply Iff.trans _ Nat.not_lt.symm
  apply le_sqrt_iff

def sqrt_le_of_le_sq (n: Nat) : ∀{x}, n ≤ x * x -> sqrt n ≤ x := by
  intro x h
  apply (le_iff_sq_le _ _).mpr
  apply Nat.le_trans _ h
  apply sqrt_sq_le_self

def pair (a b: Nat) :=
  if a < b then b * b + a else a * a + a + b

def unpair (n: Nat) : Nat × Nat :=
  have s := sqrt n
  if n - s * s < s then (n - s * s, s) else (s, n - s * s - s)

end Nat
