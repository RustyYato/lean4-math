import Math.Data.Rat.Basic
import Math.Data.StdInt.Order

def Fract.LE (a b: Fract) := a.num * b.den ≤ b.num * a.den
def Fract.LT (a b: Fract) := a.num * b.den < b.num * a.den

local notation "⟦" f "⟧" => QuotLike.mk (Q := ℚ) f

instance : LT Fract := ⟨Fract.LT⟩
instance : LE Fract := ⟨Fract.LE⟩

instance : LT ℚ := ⟨fun a b => a.LT b.toFract⟩
instance : LE ℚ := ⟨fun a b => a.LE b.toFract⟩

@[simp]
def Fract.le_def (a b: Fract) : (a ≤ b) = (a.num * b.den ≤ b.num * a.den) := rfl
@[simp]
def Fract.lt_def (a b: Fract) : (a < b) = (a.num * b.den < b.num * a.den) := rfl
def Rat.le_def (a b: ℚ) : (a ≤ b) = (a.num * b.den ≤ b.num * a.den) := rfl
def Rat.lt_def (a b: ℚ) : (a < b) = (a.num * b.den < b.num * a.den) := rfl

def Fract.LE.spec (a b c d: Fract) : a ≈ c -> b ≈ d -> a ≤ b -> c ≤ d := by
  intro ac bd ab
  replace ab : a.num * _ ≤ _ *_ := ab
  show c.num * _ ≤ _ * _
  apply Int.le_of_mul_le_mul_right (a := (a.den * b.den))
  rw [Int.mul_assoc, Int.mul_left_comm d.den]
  rw [Int.mul_assoc, Int.mul_comm a.den b.den, Int.mul_left_comm c.den]
  rw [←Int.mul_assoc, ←Int.mul_assoc d.num, ←ac, ←bd]
  rw [Int.mul_assoc, Int.mul_comm d.den b.den, Int.mul_left_comm c.den]
  rw [Int.mul_assoc, Int.mul_comm c.den a.den, Int.mul_left_comm d.den]
  rw [←Int.mul_assoc, ←Int.mul_assoc b.num, Int.mul_comm c.den]
  apply Int.mul_le_mul_of_nonneg_right
  assumption
  rw [Int.ofNat_mul_ofNat]
  apply Int.ofNat_zero_le
  rw [Int.ofNat_mul_ofNat]
  apply Int.ofNat_lt.mpr
  apply Nat.mul_pos
  exact a.den_pos
  exact b.den_pos

def Fract.LT.spec (a b c d: Fract) : a ≈ c -> b ≈ d -> a < b -> c < d := by
  intro ac bd ab
  apply lt_of_not_le (α := Int)
  intro h
  apply not_le_of_lt (α := Int) ab
  apply Fract.LE.spec d c b a
  symm; assumption
  symm; assumption
  assumption

def Rat.mk_le (a b: Fract) : (⟦a⟧ ≤ ⟦b⟧) ↔ a ≤ b := by
  apply Iff.intro
  apply Fract.LE.spec
  symm; apply Fract.reduce.spec
  symm; apply Fract.reduce.spec
  apply Fract.LE.spec
  apply Fract.reduce.spec
  apply Fract.reduce.spec

def Rat.mk_lt (a b: Fract) : (⟦a⟧ < ⟦b⟧) ↔ a < b := by
  apply Iff.intro
  apply Fract.LT.spec
  symm; apply Fract.reduce.spec
  symm; apply Fract.reduce.spec
  apply Fract.LT.spec
  apply Fract.reduce.spec
  apply Fract.reduce.spec

instance (a b: Fract) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.num * _ ≤ _ * _))
instance (a b: Fract) : Decidable (a < b) := inferInstanceAs (Decidable (a.num * _ < _ * _))

instance (a b: ℚ) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.toFract ≤ b.toFract))
instance (a b: ℚ) : Decidable (a < b) := inferInstanceAs (Decidable (a.toFract < b.toFract))

instance : Min Fract := minOfLe
instance : Max Fract := maxOfLe
instance : Min ℚ := minOfLe
instance : Max ℚ := maxOfLe

instance : IsLinearOrder ℚ where
  lt_iff_le_and_not_le := by
    intro a b
    apply lt_iff_le_and_not_le (α := Int)
  lt_or_le := by
    intro a b
    apply lt_or_le (α := Int)
  le_antisymm := by
    intro a b ab ba
    quot_ind (a b)
    rw [Rat.mk_le] at ab ba
    have := le_antisymm (α := Int) ab ba
    apply quot.sound
    assumption
  le_trans := by
    intro a b c
    intro ab bc
    replace ab : a.num * _ ≤ _ * _ := ab
    replace bc : b.num * _ ≤ _ * _ := bc
    show a.num * _ ≤ _ * _
    replace ab := Int.mul_le_mul_of_nonneg_right (c := c.den) ab (Int.ofNat_zero_le _)
    replace bc := Int.mul_le_mul_of_nonneg_right (c := a.den) bc (Int.ofNat_zero_le _)
    rw [Int.mul_right_comm]  at bc
    have ac := le_trans ab bc
    repeat rw [Int.mul_right_comm _ b.den] at ac
    apply Int.le_of_mul_le_mul_right ac
    have := b.den_pos
    exact Int.ofNat_pos.mpr this

instance : IsDecidableLinearOrder ℚ where

namespace Rat

def neg_le_neg_iff {a b: ℚ} : a ≤ b ↔ -b ≤ -a := by
  unfold LE.le
  simp [instLERat, Fract.LE]
  apply Iff.intro
  apply Int.neg_le_neg
  intro h
  have := Int.neg_le_neg h
  simp at this
  assumption

def neg_lt_neg_iff {a b: ℚ} : a < b ↔ -b < -a := by
  apply Iff.trans lt_iff_not_le
  apply Iff.trans _ lt_iff_not_le.symm
  apply Iff.not_iff_not
  apply neg_le_neg_iff

def nonneg_iff_sign_nonneg {a: ℚ} : 0 ≤ a ↔ 0 ≤ a.sign := by
  obtain ⟨⟨a, _, _ ⟩, _⟩ := a
  simp [sign]
  conv => { lhs; unfold LE.le }
  show _ * _ ≤ _ * _ ↔ _
  erw [Int.zero_mul, Int.mul_one]

def nonpos_iff_sign_nonpos {a: ℚ} : a ≤ 0 ↔ a.sign ≤ 0 := by
  obtain ⟨⟨a, _, _ ⟩, _⟩ := a
  simp [sign]
  conv => { lhs; unfold LE.le }
  show _ * _ ≤ _ * _ ↔ _
  simp
  erw [Int.zero_mul, Int.mul_one]
  have : ∀{a b: Int}, a ≤ b ↔ -b ≤ -a := by
    intros a b
    apply Iff.intro Int.neg_le_neg
    intro h
    rw [←Int.neg_neg a, ←Int.neg_neg b]
    exact Int.neg_le_neg h
  rw [this, this (a := a.sign), ←Int.sign_neg]
  apply Int.sign_nonneg.symm

def pos_iff_sign_pos {a: ℚ} : 0 < a ↔ 0 < a.sign := by
  apply Iff.trans lt_iff_not_le
  apply Iff.trans _ lt_iff_not_le.symm
  apply Iff.not_iff_not
  apply nonpos_iff_sign_nonpos

def neg_iff_sign_neg {a: ℚ} : a < 0 ↔ a.sign < 0 := by
  apply Iff.trans lt_iff_not_le
  apply Iff.trans _ lt_iff_not_le.symm
  apply Iff.not_iff_not
  apply nonneg_iff_sign_nonneg

def eq_zero_iff_sign_eq_zero {a: ℚ} : a = 0 ↔ a.sign = 0 := by
  apply Iff.intro
  intro h; subst h; rfl
  intro h
  apply le_antisymm
  apply nonpos_iff_sign_nonpos.mpr
  rw [h]
  apply nonneg_iff_sign_nonneg.mpr
  rw [h]

def abs_nonneg (a: ℚ) : 0 ≤ ‖a‖ := by
  apply nonneg_iff_sign_nonneg.mpr
  rw [abs_sign]
  obtain ⟨⟨a, _, _ ⟩, _⟩ := a
  simp [sign]
  apply Int.ofNat_zero_le

def abs_pos (a: ℚ) : a ≠ 0 -> 0 < ‖a‖ := by
  intro h
  apply lt_of_not_le
  intro g
  have := eq_zero_iff_abs_eq_zero.mpr (le_antisymm g (abs_nonneg _))
  contradiction

def add_le_add_right {a b k: ℚ} : a ≤ b ↔ a + k ≤ b + k := by
  quot_ind (a b k)
  simp [mk_le, Int.add_mul]
  have : k.num * ↑a.den * (↑b.den * ↑k.den) = k.num * ↑b.den * (↑a.den * ↑k.den) := by ac_rfl
  rw [this]; clear this
  apply Iff.trans _ (Int.add_le_add_iff_right _).symm
  have : ∀a b: Int, a * ↑k.den * (b * ↑k.den) = a * b * (↑k.den * ↑k.den) := by intros; ac_rfl
  rw [this, this]; clear this
  repeat rw [Int.ofNat_mul_ofNat]
  apply Iff.intro
  intro h
  refine Int.mul_le_mul_of_nonneg_right ?_ ?_
  assumption
  apply Int.ofNat_zero_le
  intro h
  apply Int.le_of_mul_le_mul_right
  assumption
  apply Int.ofNat_lt.mpr
  apply Nat.mul_pos <;> exact k.den_pos

def add_le_add_left {a b k: ℚ} : a ≤ b ↔ k + a ≤ k + b := by
  rw [add_comm k, add_comm k]
  exact add_le_add_right

def add_lt_add_right {a b k: ℚ} : a < b ↔ a + k < b + k := by
  apply Iff.trans lt_iff_not_le
  apply Iff.trans _ lt_iff_not_le.symm
  apply Iff.not_iff_not
  apply add_le_add_right

def add_lt_add_left {a b k: ℚ} : a < b ↔ k + a < k + b := by
  apply Iff.trans lt_iff_not_le
  apply Iff.trans _ lt_iff_not_le.symm
  apply Iff.not_iff_not
  apply add_le_add_left

def add_le_add {a b c d: ℚ} : a ≤ c -> b ≤ d -> a + b ≤ c + d := by
  intro ac bd
  apply le_trans
  apply add_le_add_right.mp
  assumption
  apply add_le_add_left.mp
  assumption

def add_lt_add {a b c d: ℚ} : a < c -> b < d -> a + b < c + d := by
  intro ac bd
  apply lt_trans
  apply add_lt_add_right.mp
  assumption
  apply add_lt_add_left.mp
  assumption

def add_lt_add_of_lt_of_le {a b c d: ℚ} : a < c -> b ≤ d -> a + b < c + d := by
  intro ac bd
  apply lt_of_lt_of_le
  apply add_lt_add_right.mp
  assumption
  apply add_le_add_left.mp
  assumption

def add_lt_add_of_le_of_lt {a b c d: ℚ} : a ≤ c -> b < d -> a + b < c + d := by
  intro ac bd
  apply lt_of_le_of_lt
  apply add_le_add_right.mp
  assumption
  apply add_lt_add_left.mp
  assumption

def abs_def (a: ℚ) : ‖a‖ = if a < 0 then -a else a := by
  obtain ⟨⟨n, d, d_pos⟩, red⟩ := a
  apply Rat.congr
  simp [neg_iff_sign_neg, sign]
  cases n
  rw [if_neg]
  rfl
  intro h
  rename_i n
  cases n <;> contradiction
  rfl
  split <;> rfl

def add_neg_lt_left (a b: ℚ) : b < 0 -> a + b < a := by
  intro bneg
  conv => { rhs; rw [←add_zero a] }
  apply add_lt_add_of_le_of_lt
  rfl
  assumption

def left_le_add_nonneg (a b: ℚ) : 0 ≤ b -> a ≤ a + b := by
  intro bneg
  conv => { lhs; rw [←add_zero a] }
  apply add_le_add
  rfl
  assumption

def abs_add_le_add_abs.helper (a b: ℚ) : a < 0 -> 0 ≤ b -> ‖a + b‖ ≤ -a + b := by
  intro a_neg b_nonneg
  rw [abs_def]
  split
  rw [neg_add]
  apply add_le_add
  rfl
  apply le_trans _ b_nonneg
  apply neg_le_neg_iff.mpr
  rw [neg_neg]
  assumption
  apply add_le_add
  apply le_trans (le_of_lt a_neg)
  apply neg_le_neg_iff.mpr
  rw [neg_neg]
  apply le_of_lt
  assumption
  rfl

def abs_add_le_add_abs (a b: ℚ) : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := by
  rw [abs_def a, abs_def b]
  split <;> split <;> rename_i h g
  rw [abs_def, if_pos, neg_add]
  rw [←add_zero 0]
  apply add_lt_add <;> assumption
  · apply abs_add_le_add_abs.helper
    assumption
    apply le_of_not_lt
    assumption
  · rw [add_comm a, add_comm a]
    apply abs_add_le_add_abs.helper
    assumption
    apply le_of_not_lt
    assumption
  rw [abs_def, if_neg]
  apply not_lt_of_le
  rw [←add_zero 0]
  apply add_le_add <;> (apply le_of_not_lt; assumption)

def abs_add_lt_add_abs_left_neg (a b: ℚ) :
  a < 0 -> 0 < b -> ‖a + b‖ < ‖a‖ + ‖b‖ := by
  intro aneg bpos
  apply lt_of_le_of_ne
  apply abs_add_le_add_abs
  intro eq
  rw [abs_def a, abs_def b] at eq
  rw [if_pos aneg, if_neg (not_lt_of_le (le_of_lt bpos)), abs_def] at eq
  split at eq
  rw [neg_add] at eq
  have := add_cancel_left.mpr eq
  cases eq_zero_of_eq_neg_self _ this.symm
  contradiction
  have := add_cancel_right.mpr eq
  cases eq_zero_of_eq_neg_self _ this
  contradiction

def abs_add_lt_add_abs_right_neg (a b: ℚ) :
  0 < a -> b < 0 -> ‖a + b‖ < ‖a‖ + ‖b‖ := by
  intro apos bneg
  rw [add_comm a, add_comm ‖a‖]
  apply abs_add_lt_add_abs_left_neg <;> assumption

def lt_of_mul_right_pos {a b k: ℚ} : 0 < k -> (a < b ↔ a * k < b * k) := by
  intro k_pos
  replace k_pos : ⟦0⟧ < k := k_pos
  quot_ind (a b k)
  simp [mk_lt]
  simp [mk_lt] at k_pos
  erw [Int.zero_mul, Int.mul_one] at k_pos
  rw [Int.mul_assoc _ k.num, Int.mul_left_comm k.num, ←Int.mul_assoc a.num]
  rw [Int.mul_assoc _ k.num, Int.mul_left_comm k.num, ←Int.mul_assoc b.num]
  apply Iff.intro
  intro h
  refine Int.mul_lt_mul_of_pos_right h ?_
  apply Int.mul_pos
  assumption
  apply Int.ofNat_pos.mpr
  exact k.den_pos
  intro h
  apply Int.lt_of_mul_lt_mul_right h
  apply le_of_lt
  apply Int.mul_pos
  assumption
  apply Int.ofNat_pos.mpr
  exact k.den_pos

def lt_of_mul_left_pos {a b k: ℚ} : 0 < k -> (a < b ↔ k * a < k * b) := by
  intro k_pos
  rw [mul_comm k, mul_comm k]
  apply lt_of_mul_right_pos
  assumption

def le_of_mul_right_pos {a b k: ℚ} : 0 < k -> (a ≤ b ↔ a * k ≤ b * k) := by
  intro k_pos
  apply Iff.trans le_iff_not_lt
  apply Iff.trans _ le_iff_not_lt.symm
  apply Iff.not_iff_not
  apply lt_of_mul_right_pos
  assumption

def le_of_mul_left_pos {a b k: ℚ} : 0 < k -> (a ≤ b ↔ k * a ≤ k * b) := by
  intro k_pos
  apply Iff.trans le_iff_not_lt
  apply Iff.trans _ le_iff_not_lt.symm
  apply Iff.not_iff_not
  apply lt_of_mul_left_pos
  assumption

def mul_le_mul_of_right_nonneg (a b k: ℚ) : 0 ≤ k -> a ≤ b -> a * k ≤ b * k := by
  intro k_nonneg ab
  rcases lt_or_eq_of_le k_nonneg with k_pos | k_eq_ero
  apply (le_of_mul_right_pos _).mp
  assumption
  assumption
  subst k
  rw [mul_zero, mul_zero]

def mul_le_mul_of_left_nonneg (a b k: ℚ) : 0 ≤ k -> a ≤ b -> k * a ≤ k * b := by
  rw [mul_comm k, mul_comm k]
  apply mul_le_mul_of_right_nonneg

def mul_lt_mul_of_left_pos (a b k: ℚ) : 0 < k -> a < b -> k * a < k * b := by
  rw [mul_comm k, mul_comm k]
  intro k_pos a_lt_b
  apply lt_of_le_of_ne
  apply mul_le_mul_of_right_nonneg
  apply le_of_lt; assumption
  apply le_of_lt; assumption
  intro ak_eq_bk
  cases (mul_cancel_right (ne_of_lt k_pos).symm).mpr ak_eq_bk
  exact lt_irrefl a_lt_b

def inv_pos (a: ℚ) (h: a ≠ 0 := by invert_tactic) : 0 < a ↔ 0 < a⁻¹ := by
  apply Iff.intro
  intro h
  apply (lt_of_mul_right_pos (a := 0) (b := a⁻¹) (k := a) h).mpr
  rw [zero_mul, inv_self_mul]
  decide
  intro h
  apply (lt_of_mul_right_pos (a := 0) (b := a) (k := a⁻¹) h).mpr
  rw [zero_mul, mul_inv_self]
  decide

def div_pos {a b: ℚ} : 0 < a -> (h: 0 < b) -> 0 < a /? b~(by
  symm; apply ne_of_lt; assumption) := by
  intro apos bpos
  rw [div_eq_mul_inv]
  conv => { lhs; rw [←mul_zero a] }
  apply (lt_of_mul_left_pos _).mp
  apply (inv_pos _ _).mp
  assumption
  assumption

def neg_le_self_of_nonneg (a: ℚ) : 0 ≤ a -> -a ≤ a := by
  intro h
  apply le_trans _ h
  apply neg_le_neg_iff.mpr
  rwa [neg_neg]

def self_le_neg_of_nonpos (a: ℚ) : a ≤ 0 -> a ≤ -a := by
  intro h
  apply le_trans h
  apply neg_le_neg_iff.mpr
  rwa [neg_neg]

def sub_abs_self_sub (a b: ℚ) : a - ‖a - b‖ ≤ b := by
  rw [abs_def]
  split
  rw [sub_eq_add_neg, neg_neg]
  conv => { rhs; rw [←add_zero b] }
  apply add_le_add
  apply add_le_add_right.mpr
  apply le_of_lt
  rwa [add_neg_self b, ←sub_eq_add_neg]
  apply le_of_lt; assumption
  rw [sub_eq_add_neg, sub_eq_add_neg, neg_add,
    neg_neg, ←add_assoc, add_neg_self, zero_add]

def sub_le_sub (a b c d: ℚ) : a ≤ c -> d ≤ b -> a - b ≤ c - d := by
  intro ab db
  rw [sub_eq_add_neg, sub_eq_add_neg]
  apply add_le_add
  assumption
  apply neg_le_neg_iff.mp
  assumption

def sub_half (a: ℚ) : a - a /? 2 = a /? 2 := by
  conv => { lhs; lhs; rw [←mul_div_cancel 2 a (by decide)] }
  rw [mul_two, sub_eq_add_neg, add_assoc, add_neg_self, add_zero]

def add_half (a: ℚ) : a = a /? 2 + a /? 2 := by
  rw [←mul_two, mul_div_cancel]

end Rat
