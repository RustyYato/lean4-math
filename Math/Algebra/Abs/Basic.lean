import Math.Algebra.Abs.Defs
import Math.Algebra.Field.Basic

section

variable [AbsoluteValue α β] [LE β] [LT β]
  [AddMonoidOps α] [Mul α]
  [AddMonoidOps β] [Mul β]
  [IsNonUnitalNonAssocSemiring α]
  [IsOrderedNonUnitalNonAssocSemiring β]
  [IsLawfulAbs α]

def abs_ne_zero (a: α) : a ≠ 0 -> ‖a‖ ≠ 0 := by
  intro h g; apply h
  apply of_abs_eq_zero
  assumption

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply abs_ne_zero <;> invert_tactic)

end

section

variable
  [AbsoluteValue α β] [LE β] [LT β]
  [SemiringOps α] [SemiringOps β]
  [IsSemiring α] [IsOrderedSemiring β]
  [IsLawfulAbs α] [IsLeftCancel₀ β]

-- if we are in a non-trivial domain,
-- then the absolute value of one = 1
def abs_one [IsNontrivial α] : ‖(1: α)‖ = 1 := by
  have : ‖(1: α)‖ * ‖(1: α)‖ = ‖(1: α)‖ := by rw [←abs_mul, mul_one]
  rw (occs := [3]) [←mul_one ‖(1: α)‖] at this
  rcases subsingleton_or_nontrivial β
  apply Subsingleton.allEq
  refine mul_left_cancel₀ ?_ this
  intro h
  exact zero_ne_one α (of_abs_eq_zero h).symm

def abs_npow [IsNontrivial α] (a: α) (n: ℕ) : ‖a ^ n‖ = ‖a‖ ^ n := by
  induction n with
  | zero => rw [npow_zero, npow_zero, abs_one]
  | succ n ih => rw [npow_succ, abs_mul, ih, npow_succ]

def abs_npow_succ (a: α) (n: Nat) : ‖a ^ (n + 1)‖ = ‖a‖ ^ (n + 1) := by
  induction n with
  | zero => rw [npow_one, npow_one]
  | succ n ih => rw [npow_succ, npow_succ, abs_mul, ←npow_succ, ih, npow_succ, npow_succ, npow_succ]

def abs_unit [IsNontrivial α] (u: Units α) : Units β where
  val := ‖u.val‖
  inv := ‖u.inv‖
  val_mul_inv := by rw [←abs_mul, u.val_mul_inv, abs_one]
  inv_mul_val := by rw [←abs_mul, u.inv_mul_val, abs_one]

end

section

variable
  [AbsoluteValue α β] [LE β] [LT β]
  [AddGroupOps α] [AddMonoidOps β]
  [IsAddGroup α][IsOrderedAddCommMonoid β]
  [IsLawfulNorm α]

def abs_neg (a: α) : ‖-a‖ = ‖a‖ := by
  apply IsLawfulNorm.abs_eq_of_add_eq_zero
  rw [neg_add_cancel]

def abs_sub_comm (a b: α) : ‖a - b‖ = ‖b - a‖ := by
  rw [←abs_neg, neg_sub]

end

section

variable
  [AbsoluteValue α β] [LE β] [LT β]
  [FieldOps α] [FieldOps β]
  [IsNonCommSemifield α] [IsNonCommSemifield β]
  [IsOrderedSemiring β] [IsLawfulAbs α]

def abs_inv? (a: α) (h: a ≠ 0) : ‖a⁻¹?‖ = ‖a‖⁻¹? := by
  symm; apply inv?_eq_of_mul_left
  rw [←abs_mul, mul_inv?_cancel, abs_one]

def abs_div? (a b: α) (h: b ≠ 0) : ‖a /? b‖ = ‖a‖ /? ‖b‖ := by
  rw [div?_eq_mul_inv?, div?_eq_mul_inv?, abs_mul, abs_inv?]

end
