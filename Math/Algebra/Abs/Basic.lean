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
  [IsNontrivial α]

-- if we are in a non-trivial domain,
-- then the absolute value of one = 1
def abs_one : ‖(1: α)‖ = 1 := by
  have : ‖(1: α)‖ * ‖(1: α)‖ = ‖(1: α)‖ := by rw [←abs_mul, mul_one]
  rw (occs := [3]) [←mul_one ‖(1: α)‖] at this
  rcases subsingleton_or_nontrivial β
  apply Subsingleton.allEq
  refine mul_left_cancel₀ ?_ this
  intro h
  exact zero_ne_one α (of_abs_eq_zero h).symm

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
