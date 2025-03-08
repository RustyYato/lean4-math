import Math.Logic.Basic
import Math.Function.Basic

namespace Nat

def le_iff_exists_sum (a b: Nat) : a ≤ b ↔ ∃k, b = a + k := by
  apply Iff.intro
  intro h
  exists b - a
  rw [Nat.add_sub_cancel' h]
  intro ⟨k, h⟩
  subst b
  apply Nat.le_add_right

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

def PerfectSquare (a: Nat) := ∃b, b * b = a

def sqrt_eq_of_sq_eq (a b: Nat) :
  b * b = a -> sqrt a = b := by
  intro h
  subst a
  symm; apply (sqrt_eq_iff _ _).mpr
  apply And.intro
  apply Nat.le_refl
  apply (lt_iff_sq_lt _ _).mp
  apply Nat.lt_succ_self

def sqrt_sq (a: Nat) : sqrt (a * a) = a := by
  rw [sqrt_eq_of_sq_eq]
  rfl

def sqrt_of_perfect_square (a: Nat) :
  sqrt a * sqrt a = a ↔ PerfectSquare a := by
  apply Iff.intro
  intro h
  exists sqrt a
  intro ⟨b, prf⟩
  conv => { rhs; rw [←prf] }
  suffices sqrt a = b by rw [this]
  apply sqrt_eq_of_sq_eq
  assumption

def square_add (a b: Nat) : (a + b) * (a + b) = a * a + 2 * a * b + b * b := by
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_assoc, Nat.two_mul]
  ac_rfl

def square_sub (a b: Nat) (h: b ≤ a) : (a - b) * (a - b) = a * a + b * b - 2 * a * b := by
  apply Int.ofNat_inj.mp
  rw [Nat.two_mul, Nat.add_mul, Int.ofNat_sub]
  simp [Int.ofNat_sub h, Int.sub_mul, Int.mul_sub]
  rw [Int.mul_comm b a]
  omega
  rw [le_iff_exists_sum] at *
  obtain ⟨k, h⟩ := h
  subst a
  exists k * k
  simp [Nat.add_mul, Nat.mul_add]
  ac_rfl

def two_dvd_mul_succ (n: Nat) : 2 ∣ n * (n + 1) := by
  cases Nat.mod_two_eq_zero_or_one n <;> rename_i h
  apply Nat.dvd_trans
  apply Nat.dvd_of_mod_eq_zero
  assumption
  apply Nat.dvd_mul_right
  apply flip Nat.dvd_trans
  apply Nat.dvd_mul_left
  apply Nat.dvd_of_mod_eq_zero
  rw [Nat.add_mod, h]

def sqrt_add_eq (n : Nat) (h : a ≤ 2 * n) : sqrt (n * n + a) = n := by
  apply Nat.le_antisymm
  apply le_of_lt_succ
  apply (sqrt_lt_iff _).mpr
  rw [succ_eq_add_one, square_add, Nat.add_assoc]
  apply Nat.add_lt_add_left
  apply Nat.lt_succ_of_le
  rw [Nat.mul_one]
  assumption
  rw [le_sqrt_iff]
  apply Nat.le_add_right

def lt_succ_sqrt (n : Nat) : n < succ (sqrt n) * succ (sqrt n) :=
  ((sqrt_eq_iff _ _).mp rfl).right

def sqrt_le_add (n : Nat) : n ≤ sqrt n * sqrt n + sqrt n + sqrt n := by
  rw [←succ_mul]
  apply le_of_lt_succ
  apply lt_succ_sqrt

def sqrt_zero : sqrt 0 = 0 := by decide +kernel
def sqrt_one : sqrt 1 = 1 := by decide +kernel

/-- returns the largest number `n` such at `n * (n + 1) / 2 ≤ a` --/
def inv_triangle (a: Nat) : Nat :=
  (sqrt (8 * a + 1) - 1) / 2

/-- the nth triangle number --/
def triangle (n: Nat) := n * (n + 1) / 2

def triangle_zero : triangle 0 = 0 := rfl
def triangle_succ (n: Nat) : triangle (n + 1) = triangle n + (n + 1) := by
  unfold triangle
  apply Nat.mul_left_cancel (n := 2) (by decide)
  rw [Nat.mul_add 2, Nat.mul_div_cancel', Nat.mul_div_cancel']
  any_goals apply two_dvd_mul_succ
  simp [Nat.mul_add, Nat.add_mul]
  omega

def inv_triangle_helper : 8 * (triangle n) + 1 = (2 * n + 1) * (2 * n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [triangle_succ, Nat.add_comm n.triangle, Nat.mul_add,
      Nat.add_assoc, ih]
    simp [Nat.add_mul, Nat.mul_add]
    omega

def triangle_left_inv: Function.IsLeftInverse inv_triangle triangle := by
  intro n
  unfold inv_triangle
  rw [inv_triangle_helper, sqrt_sq, Nat.add_sub_cancel, Nat.mul_div_cancel_left]
  decide

def sqrt_sq_add (n: Nat) : ∃m, n = n.sqrt * n.sqrt + m ∧ m ≤ 2 * n.sqrt := by
  have := sqrt_sq_le_self n
  rw [Nat.le_iff_exists_sum] at this
  obtain ⟨m, eq⟩ := this
  exists m
  apply And.intro eq
  apply Nat.le_of_lt_succ
  show m < 2 * _ + 1
  apply Nat.lt_of_add_lt_add_left
  rw [←eq, Nat.add_succ]
  apply Nat.lt_succ_of_le
  rw [Nat.two_mul, ←Nat.add_assoc]
  apply sqrt_le_add

def sq_add_le_sq_succ {n k: Nat} :
  k < 4 * n + 4 ↔ n * n + k < (n + 2) * (n + 2) := by
  apply Iff.intro
  intro h
  simp [Nat.mul_add, Nat.add_mul]
  omega
  intro h
  simp [Nat.mul_add, Nat.add_mul] at h
  rw [Nat.add_assoc] at h
  replace h := Nat.lt_of_add_lt_add_left h
  omega

-- def inv_triangle_add (h: k ≤ n) : inv_triangle (triangle n + k) = n := by
--   unfold inv_triangle
--   rw [Nat.add_comm _ k, Nat.mul_add, Nat.add_assoc, Nat.add_comm, inv_triangle_helper]
--   rw [Nat.div_eq_iff]
--   apply And.intro
--   rw [←Nat.pred_eq_sub_one, Nat.pred_le_iff_le_succ, Nat.succ_eq_add_one]
--   rw [←Nat.lt_succ, sqrt_lt_iff]
--   rw [Nat.sub_add_cancel, Nat.mul_comm _ 2]
--   show _ < (2 * n + 3) * (2 * n + 3)
--   apply sq_add_le_sq_succ.mp
--   rw [Nat.mul_add]
--   apply Nat.lt_of_succ_le
--   apply Nat.succ_le_succ
--   rw [←Nat.mul_assoc]
--   apply Nat.le_trans
--   apply Nat.mul_le_mul_left
--   assumption
--   apply Nat.le_add_right
--   apply Nat.succ_le_succ
--   apply Nat.zero_le
--   rw [Nat.sub_one]
--   apply Nat.le_pred_of_lt
--   -- apply Nat.lt_sqrt
--   sorry






--   -- rw [sqrt_add_eq, Nat.add_sub_cancel, Nat.mul_div_cancel_left]
--   -- decide

--   -- have ⟨i, k_eq, i_le⟩ := sqrt_sq_add k
--   -- rw [k_eq]



--   sorry

def triangle_strict_monotone (a b: Nat) : a < b -> triangle a < triangle b := by
  intro lt
  induction b generalizing a with
  | zero => contradiction
  | succ b ih =>
    rw [triangle_succ]
    cases a with
    | zero => apply Nat.zero_lt_succ
    | succ a =>
      rw [triangle_succ]
      apply Nat.add_lt_add
      apply ih
      apply Nat.lt_of_succ_lt_succ
      assumption
      assumption

def triangle_inj : Function.Injective triangle := triangle_left_inv.Injective

def pair (a b: Nat) :=
  triangle (a + b) + a

def unpair (x: Nat): Nat × Nat :=
  let ab := inv_triangle x
  let a := x - triangle ab
  let b := ab - a
  ⟨a, b⟩

def unpair_pair (x: Nat) : pair (unpair x).1 (unpair x).2 = x := sorry

-- def sub_mul (a b k: Nat) : (a - b) * k = a * k - b * k := by
--   by_cases h:b < a
--   · apply Int.ofNat.inj
--     simp
--     repeat rw [Int.ofNat_sub]
--     repeat rw [Int.ofNat_mul]
--     rw [Int.sub_mul]
--     apply Nat.mul_le_mul_right
--     apply Nat.le_of_lt
--     assumption
--     apply Nat.le_of_lt
--     assumption
--   · replace h := Nat.le_of_not_lt h
--     rw [Nat.sub_eq_zero_iff_le.mpr h, Nat.sub_eq_zero_iff_le.mpr, Nat.zero_mul]
--     apply Nat.mul_le_mul_right
--     assumption
-- def mul_sub (a b k: Nat) : k * (a - b) = k * a - k * b := by
--   iterate 3 rw [Nat.mul_comm k]
--   rw [sub_mul]

def unpair_pair.helper₀ (a b: Nat) (h: b ≤ a) :
  (a - b) * (a - b) + 2 * a * b = a * a + b * b := by
  apply Int.ofNat.inj
  rw [Nat.two_mul, Int.ofNat_eq_coe, Int.ofNat_eq_coe]
  simp [Int.ofNat_sub h, Int.sub_mul, Int.mul_sub]
  simp [Int.sub_eq_add_neg, Int.mul_comm b, Int.neg_add, Int.add_mul]
  omega

def lt_sqrt_iff (a b: Nat) :
  b < sqrt a ↔ (b + 1) * (b + 1) ≤ a := by
  apply Iff.trans Nat.succ_le.symm
  show b + 1 ≤ _ ↔ _
  apply Iff.trans (le_sqrt_iff _)
  rfl

def sqrt_pos (a: Nat) : 0 < a -> 0 < a.sqrt := by
  intro h
  rw [lt_sqrt_iff]
  exact h

-- def div_add_div_le (a b k: Nat) : a / k + b / k ≤ (a + b) / k := by
--   cases k
--   iterate 3 rw [Nat.div_zero]
--   apply Nat.le_refl
--   rename_i k
--   rw [Nat.le_div_iff_mul_le (Nat.zero_lt_succ _)]
--   rw [Nat.add_mul]
--   apply Nat.add_le_add
--   apply Nat.div_mul_le_self
--   apply Nat.div_mul_le_self

-- def pair_unpair (a b: Nat) : unpair (pair a b) = ⟨a, b⟩ := by
--   unfold pair unpair
--   dsimp
--   rw [inv_triangle_add, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
--   apply Nat.le_add_right
  -- generalize hw:a + b = w
  -- generalize ht:(w * (w + 1)) / 2 = t
  -- generalize hz:t + a = z
  -- have : 2 ∣ w * (w + 1) := two_dvd_mul_succ w
  -- have sqrt_eq : (8 * t + 1).sqrt = 2 * w + 1 := by
  --   subst t
  --   show (4 * 2 * _ + _).sqrt = _
  --   rw [Nat.mul_assoc, Nat.mul_div_cancel' this]
  --   rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
  --   apply sqrt_eq_of_sq_eq
  --   simp [Nat.mul_add, Nat.add_mul]
  --   rw [←Nat.add_assoc, Nat.add_assoc (_ * _)]
  --   congr 2
  --   ac_rfl
  --   rw [←Nat.two_mul, ←Nat.mul_assoc]
  -- unfold unpair
  -- dsimp
  -- suffices ((8 * z + 1).sqrt - 1) / 2 = w by
  --   rw [this]; clear this
  --   subst z; subst t; subst w
  --   congr
  --   rw [Nat.add_sub_cancel_left]
  --   omega
  -- apply Nat.eq_of_le_of_lt_succ
  -- · apply (Nat.le_div_iff_mul_le (by decide)).mpr
  --   apply Nat.le_pred_of_lt
  --   apply Nat.lt_of_succ_le
  --   show w * 2 + 1 ≤ _
  --   apply (Nat.le_sqrt_iff _).mpr
  --   rw [square_add, Nat.mul_one, Nat.mul_one]
  --   apply Nat.succ_le_succ
  --   have : w * 2 * (w * 2) + 2 * (w * 2)
  --     = 2 * 2 * (w * w) + 2 * 2 * (w * 1) := by ac_rfl
  --   rw [this]; clear this
  --   rw [←Nat.mul_add, ←Nat.mul_add]
  --   show _ ≤ 4 * 2 * _
  --   rw [Nat.mul_assoc 4]
  --   apply Nat.mul_le_mul_left
  --   subst z
  --   subst t
  --   rw [Nat.mul_add 2, Nat.mul_div_cancel']
  --   apply Nat.le_add_right
  --   assumption
  -- · rw [Nat.div_lt_iff_lt_mul (by decide), ←Nat.add_lt_add_iff_right (k := 1), Nat.sub_add_cancel]
  --   rw [Nat.add_mul, Nat.add_assoc]
  --   show _ < _ + 3
  --   rw [Nat.sqrt_lt_iff, Nat.mul_comm _ 2, square_add, Nat.mul_comm _ 3]
  --   apply Nat.succ_lt_succ
  --   have : 2 * w * (2 * w) + 3 * (2 * (2 * w)) + 8
  --        = 2 * 2 * (w * w) + 2 * 2 * (3 * w) + 8 := by ac_rfl
  --   rw [this]; clear this; show 4 * 2 * _ < _ + 4 * 2
  --   rw [←Nat.mul_add, ←Nat.mul_add, Nat.mul_assoc]
  --   rw [Nat.mul_lt_mul_left (by decide)]
  --   show _ < _ + (1 + 2) * _ + 2 * 1
  --   rw [Nat.add_mul, Nat.mul_comm 1, ←Nat.add_assoc, ←Nat.mul_add,
  --     Nat.add_assoc, ←Nat.mul_add]
  --   subst z; subst t
  --   rw [Nat.mul_add, Nat.mul_div_cancel' (by assumption)]
  --   apply Nat.add_lt_add_left
  --   rw [Nat.mul_lt_mul_left (by decide), Nat.lt_succ]
  --   subst w; apply Nat.le_add_right
  --   apply Nat.succ_le_of_lt
  --   apply sqrt_pos
  --   apply Nat.zero_lt_succ

-- def pair_inj : Function.Injective₂ pair := by
--   intro a b c d eq
--   have : unpair (a.pair b) = unpair (c.pair d) := by rw [eq]
--   rw [pair_unpair, pair_unpair] at this
--   exact Prod.mk.inj this

-- def div_lt_div (a b k: Nat) : 0 < k -> a + (k - 1) < b -> a / k < b / k := by
--   intro kpos altb
--   rw [Nat.lt_div_iff_mul_lt]
--   apply Nat.lt_of_le_of_lt
--   apply Nat.div_mul_le_self
--   apply Nat.lt_sub_of_add_lt
--   assumption
--   assumption

-- -- def unpair_inj : Function.Injective unpair := by
-- --   suffices ∀{a b: Nat}, a < b -> unpair a ≠ unpair b by
-- --     intro a b eq
-- --     apply Decidable.byContradiction
-- --     intro h
-- --     rcases Nat.lt_or_gt_of_ne h with ab | ba
-- --     exact this ab eq
-- --     exact this ba eq.symm
-- --   intro a b a_lt_b
-- --   induction b generalizing a with
-- --   | zero => contradiction
-- --   | succ b ih =>
-- --     cases a with
-- --     | zero =>
-- --       intro h
-- --       sorry
-- --     | succ a =>
-- --       replace a_lt_b := Nat.lt_of_succ_lt_succ a_lt_b



-- --   -- unfold unpair
-- --   -- generalize ha₀:((8 * a + 1).sqrt - 1) / 2 = a₀
-- --   -- generalize hb₀:((8 * b + 1).sqrt - 1) / 2 = b₀
-- --   -- dsimp
-- --   -- intro h
-- --   -- have : ∀{a}, 1 ≤ (8 * a + 1).sqrt := by
-- --   --   intro a
-- --   --   apply Nat.succ_le_of_lt
-- --   --   apply Nat.sqrt_pos
-- --   --   apply Nat.zero_lt_succ
-- --   -- have ⟨h₀, h₁⟩ := Prod.mk.inj h; clear h






-- --   sorry

-- -- def unpair_pair' (z: Nat) : pair (unpair z).1 (unpair z).2 = z := by
-- --   apply unpair_inj
-- --   exact pair_unpair _ _

-- def unpair_pair (z: Nat) : pair (unpair z).1 (unpair z).2 = z := by
--   generalize h:z.unpair=a'
--   obtain ⟨a, b⟩ := a'
--   dsimp
--   unfold pair
--   unfold unpair at h
--   dsimp at h
--   have ⟨ha, hb⟩ := Prod.mk.inj h; clear h
--   generalize hw:((8 * z + 1).sqrt - 1) / 2 = w
--   rw [hw] at ha hb
--   subst a; subst b
--   have le_z : w * (w + 1) / 2 ≤ z := by
--     rw [Nat.mul_add, Nat.mul_one, Nat.div_le_iff_le_mul (by decide)]
--     show _ ≤ _ + 1
--     subst w
--     apply Nat.le_trans
--     apply Nat.add_le_add_right
--     apply Nat.div_mul_le_mul_div
--     conv => {
--       lhs; rhs; lhs
--       rw [←Nat.mul_div_cancel (_ - _) (n := 2) (by decide)]
--     }
--     rw [Nat.div_div_eq_div_mul]
--     apply Nat.le_trans
--     apply Nat.div_add_div_le
--     rw [Nat.div_le_iff_le_mul]
--     conv => {
--       lhs; rhs
--       rw [Nat.mul_comm, ←Nat.mul_one (sqrt _)]
--     }
--     rw [mul_sub (k := 2), ←Nat.add_sub_assoc, ←Nat.mul_assoc, unpair_pair.helper₀]
--     simp
--     erw [Nat.pred_le_iff_le_succ]
--     show _ * _ ≤ _ + 4
--     apply Nat.le_trans
--     apply sqrt_sq_le_self
--     rw [Nat.add_mul, Nat.add_assoc, Nat.mul_assoc, Nat.mul_comm z]
--     apply Nat.add_le_add_left
--     decide
--     apply Nat.succ_le_of_lt
--     apply sqrt_pos
--     apply Nat.zero_lt_succ
--     apply Nat.mul_le_mul_left
--     apply Nat.succ_le_of_lt
--     rw [Nat.mul_one]
--     apply sqrt_pos
--     apply Nat.zero_lt_succ
--     decide
--   have le_w : z - (w * (w + 1)) / 2 ≤ w := by
--     clear le_z
--     apply Nat.le_of_mul_le_mul_left (c := 2) _ (by decide)
--     rw [Nat.mul_sub, Nat.mul_div_cancel']
--     rw [Nat.sub_le_iff_le_add, Nat.mul_add, Nat.mul_one]
--     rw [Nat.add_comm, Nat.add_assoc]
--     have : w + 2 * w = 3 * w := by
--       conv => { lhs; lhs; rw [←Nat.one_mul w] }
--       rw [←Nat.add_mul]
--     rw [this]; clear this; subst w
--     apply Nat.le_of_mul_le_mul_left (c := 4) _ (by decide)
--     rw [Nat.mul_add]
--     show _ ≤ 2 * 2 * _ + 2 * 2 * _
--     rw [Nat.mul_assoc 2, ←Nat.mul_assoc 2 (_ / 2), Nat.mul_comm 2 (_ * _), Nat.mul_assoc,
--       Nat.mul_comm _ 2, Nat.mul_assoc 2 2  (3 * _), Nat.mul_left_comm 2 3]
--     rw [Nat.mul_div_self_eq_mod_sub_self, ←Nat.mul_assoc 2 3]
--     generalize hn:(8 * z + 1).sqrt - 1 = n
--     have sqrt_eq : (8 * z + 1).sqrt = n + 1 := by
--       rw [←hn, Nat.sub_add_cancel]
--       apply Nat.succ_le_of_lt
--       apply sqrt_pos
--       apply Nat.zero_lt_succ
--     have := sqrt_sq_le_self (8 * z + 1)
--     rw [sqrt_eq] at this
--     repeat sorry
--   apply Int.ofNat_inj.mp
--   simp [Int.ofNat_sub le_z, Int.ofNat_sub le_w]

--   sorry

def mul_eq_one_iff {a b: Nat} : a * b = 1 ↔ a = 1 ∧ b = 1 := by
  apply Iff.intro
  · intro h
    match a with
    | 0 => rw [Nat.zero_mul] at h; contradiction
    | 1 =>
      rw [Nat.one_mul] at h
      subst b
      trivial
    | a + 2 =>
    match b with
    | 0 => rw [Nat.mul_zero] at h; contradiction
    | b + 1 => simp [Nat.mul_add, Nat.add_mul, ←Nat.add_assoc] at h
  · intro ⟨h, g⟩
    rw [h, g]

end Nat
