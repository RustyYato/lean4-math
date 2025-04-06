import Math.Ops.Abs
import Math.Algebra.Field.Basic
import Math.Algebra.Field.Order.Basic

def abs_eq_natAbs (a: Int) : |a| = a.natAbs := by
  apply le_antisymm
  apply max_le
  omega
  omega
  apply le_max_iff.mpr
  omega

section

variable
  [LE α] [LT α] [Min α] [Max α]
  [RingOps α] [IsRing α]
  [IsOrderedSemiring α]
  [IsLinearLattice α]

def abs_zero_iff {a: α}: |a| = 0 ↔ a = 0 := by
  show |a| = 0 ↔ a = 0
  apply Iff.intro
  intro h
  rcases lt_trichotomy a 0 with g | g | g
  have : 0 < |a| := by
    unfold abs
    rw [neg_lt_neg_iff, neg_zero] at g
    apply lt_of_lt_of_le g
    apply le_max_right
  rw [h] at this
  have := lt_irrefl this
  contradiction
  assumption
  have : 0 < |a| := by
    unfold abs
    apply lt_of_lt_of_le g
    apply le_max_left
  rw [h] at this
  have := lt_irrefl this
  contradiction
  intro h
  rw [h]
  unfold abs
  rw [neg_zero, max_self]

@[simp]
def abs_one : |(1: α)| = 1 := by
  apply flip le_antisymm
  apply le_max_left
  apply max_le
  rfl
  apply flip le_trans
  apply zero_le_one
  rw [neg_le_neg_iff, neg_neg, neg_zero]
  apply zero_le_one

@[simp]
def abs_neg_one : |(-1: α)| = 1 := by
  apply flip le_antisymm
  rw (occs := [1]) [←neg_neg 1]
  apply le_max_right
  unfold abs
  rw [neg_neg]
  apply max_le
  refine neg_le_of_nonneg 1 ?_
  apply zero_le_one
  rfl

def abs_nonneg (a: α) : 0 ≤ |a| := by
  apply le_max_iff.mpr
  rw (occs := [2]) [←neg_zero]; rw [neg_le_neg_iff]
  apply le_total

def abs_pos (a: α) : a ≠ 0 -> 0 < |a| := by
  intro h
  apply lt_of_le_of_ne
  apply abs_nonneg
  symm
  intro g
  apply h
  exact abs_zero_iff.mp g

def le_abs_self (a: α) : a ≤ |a| := by
  apply le_max_left

def sub_abs_self_sub (a b: α) : a - |a - b| ≤ b := by
  rw [sub_le_iff_le_add, add_comm, le_add_iff_sub_le]
  apply le_abs_self

def abs_natCast (n: ℕ) : |(n: α)| = n := by
  rw [abs, max_eq_left]
  apply neg_le_of_nonneg
  exact natCast_nonneg n

def abs_mul (a b: α) : |a * b| = |a| * |b| := by
  unfold abs
  apply le_antisymm
  · apply max_le
    rcases le_total a 0
    · rw (occs := [1]) [←neg_neg (a * b), neg_mul_left, neg_mul_right]
      apply le_trans
      apply mul_le_mul_of_nonneg_left
      show -b ≤ b ⊔ -b
      apply le_max_right
      rw [←neg_zero]; apply neg_le_neg; assumption
      apply mul_le_mul_of_nonneg_right
      apply le_max_right
      apply abs_nonneg
    · apply le_trans
      apply mul_le_mul_of_nonneg_left
      show b ≤ b ⊔ -b
      apply le_max_left
      assumption
      apply mul_le_mul_of_nonneg_right
      apply le_max_left
      apply abs_nonneg
    rcases le_total a 0
    · rw [neg_mul_left]
      apply le_trans
      apply mul_le_mul_of_nonneg_left
      show b ≤ b ⊔ -b
      apply le_max_left
      rw [←neg_zero]; apply neg_le_neg; assumption
      apply mul_le_mul_of_nonneg_right
      apply le_max_right
      apply abs_nonneg
    · rw [neg_mul_right]
      apply le_trans
      apply mul_le_mul_of_nonneg_left
      show -b ≤ b ⊔ -b
      apply le_max_right
      assumption
      apply mul_le_mul_of_nonneg_right
      apply le_max_left
      apply abs_nonneg
  · apply le_max_iff.mpr
    rcases le_total 0 b <;> rcases le_total 0 a <;> rename_i ha hb
    left; rw [max_eq_left.mpr, max_eq_left.mpr]
    apply neg_le_of_nonneg; assumption
    apply neg_le_of_nonneg; assumption
    right; rw [max_eq_right.mpr, max_eq_left.mpr, neg_mul_left]
    apply neg_le_of_nonneg; assumption
    apply le_neg_of_nonpos; assumption
    right; rw [max_eq_left.mpr, max_eq_right.mpr, neg_mul_right]
    apply le_neg_of_nonpos; assumption
    apply neg_le_of_nonneg; assumption
    left; rw [max_eq_right.mpr, max_eq_right.mpr, ←neg_mul_right, ←neg_mul_left, neg_neg]
    apply le_neg_of_nonpos; assumption
    apply le_neg_of_nonpos; assumption

def abs_neg (a: α) : |-a| = |a| := by
  rw [←neg_one_mul, abs_mul]; simp

def abs_add_le_add_abs (a b: α): |a + b| ≤ |a| + |b| := by
  apply max_le
  apply add_le_add
  apply le_max_left
  apply le_max_left
  rw [neg_add_rev, add_comm]
  apply add_le_add
  apply le_max_right
  apply le_max_right

def abs_zero : |(0: α)| = 0 := abs_zero_iff.mpr rfl
def of_abs_eq_zero {x: α} : |x| = 0 -> x = 0 := abs_zero_iff.mp

def abs_npow [IsNontrivial α] (a: α) (n: ℕ) : |a ^ n| = |a| ^ n := by
  induction n with
  | zero => rw [npow_zero, npow_zero, abs_one]
  | succ n ih => rw [npow_succ, abs_mul, ih, npow_succ]

def abs_npow_succ (a: α) (n: Nat) : |a ^ (n + 1)| = |a| ^ (n + 1) := by
  induction n with
  | zero => rw [npow_one, npow_one]
  | succ n ih => rw [npow_succ, npow_succ, abs_mul, ←npow_succ, ih, npow_succ, npow_succ, npow_succ]

def abs_unit [IsNontrivial α] (u: Units α) : Units α where
  val := |u.val|
  inv := |u.inv|
  val_mul_inv := by rw [←abs_mul, u.val_mul_inv, abs_one]
  inv_mul_val := by rw [←abs_mul, u.inv_mul_val, abs_one]

def abs_ne_zero (a: α) : a ≠ 0 -> |a| ≠ 0 := by
  intro h g; apply h
  apply of_abs_eq_zero
  assumption

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply abs_ne_zero <;> invert_tactic)

def abs_of_nonneg (a: α) : 0 ≤ a -> |a| = a := by
  intro h
  apply max_eq_left.mpr
  exact neg_le_of_nonneg a h

def abs_of_pos (a: α) : 0 < a -> |a| = a := by
  intro h
  apply abs_of_nonneg
  apply le_of_lt; assumption

def abs_sub_comm (a b: α) : |a - b| = |b - a| := by
  rw [←neg_sub, abs_neg]

def abs_add_le_abs_sub (a b: α) : 0 ≤ a -> b ≤ 0 -> |a + b| ≤ |a - b| := by
  intro h g
  apply max_le
  apply le_max_iff.mpr
  left; rw [sub_eq_add_neg]; apply add_le_add_left
  apply le_neg_of_nonpos; assumption
  rw [neg_add_rev]
  apply le_max_iff.mpr
  left
  rw [add_comm, sub_eq_add_neg]
  apply add_le_add_right
  apply neg_le_of_nonneg
  assumption

def abs_def [DecidableLE α] (a: α) : |a| = if 0 ≤ a then a else -a := by
  rw [abs]
  split; rw [max_eq_left.mpr];
  apply neg_le_of_nonneg; assumption
  rw [max_eq_right.mpr]
  apply le_neg_of_nonpos
  rw [not_le] at *
  apply le_of_lt
  assumption

@[norm_cast]
def abs_intCast (n: ℤ) : |(n: α)| = |n| := by
  cases n with
  | ofNat n =>
    rw [intCast_ofNat, abs_eq_natAbs, Int.natAbs_ofNat,
      abs_natCast, intCast_ofNat]
  | negSucc n =>
    rw [Int.negSucc_coe, ←intCast_neg, abs_neg,
      intCast_ofNat, abs_natCast, abs_neg,
      abs_eq_natAbs, intCast_ofNat, Int.natAbs_ofNat]

end

section

variable
  [LE α] [LT α] [Min α] [Max α]
  [FieldOps α] [IsNonCommField α]
  [IsOrderedSemiring α]
  [IsLinearLattice α]

def abs_inv? (a: α) (h: a ≠ 0) : |a⁻¹?| = |a|⁻¹? := by
  symm; apply inv?_eq_of_mul_left
  rw [←abs_mul, mul_inv?_cancel, abs_one]

def abs_div? (a b: α) (h: b ≠ 0) : |a /? b| = |a| /? |b| := by
  rw [div?_eq_mul_inv?, div?_eq_mul_inv?, abs_mul, abs_inv?]

def abs_div?_lt_one (a b: α) (h: b ≠ 0) : |a /? b| < 1 ↔ |a| < |b| := by
  rw [lt_iff_mul_lt_mul_of_pos_right _ _ |b|, one_mul, ←abs_mul, div?_eq_mul_inv?]
  rw [mul_assoc, inv?_mul_cancel, mul_one]
  exact abs_pos b h

end
