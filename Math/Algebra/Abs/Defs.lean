import Math.Algebra.Semiring.Order.Defs
import Math.Algebra.GroupWithZero.Defs
import Math.Ops.Abs

class IsLawfulAbs (α: Type*) {β: outParam Type*}
  [AbsoluteValue α β] [LE β] [LT β]
  [AddMonoidOps α] [Mul α]
  [AddMonoidOps β] [Mul β]
  [IsNonUnitalNonAssocSemiring α]
  [IsOrderedNonUnitalNonAssocSemiring β]
  extends IsLinearOrder β where
  abs_nonneg (a: α): 0 ≤ ‖a‖
  abs_zero_iff {a: α}: ‖a‖ = 0 ↔ a = 0
  abs_mul (a b: α): ‖a * b‖ = ‖a‖ * ‖b‖
  abs_add_le_add_abs (a b: α): ‖a + b‖ ≤ ‖a‖ + ‖b‖

section

variable
  [AbsoluteValue α β] [LE β] [LT β]
  [AddMonoidOps α] [Mul α]
  [AddMonoidOps β] [Mul β]
  [IsNonUnitalNonAssocSemiring α]
  [IsOrderedNonUnitalNonAssocSemiring β]
  [IsLawfulAbs α]

def abs_nonneg (a: α): 0 ≤ ‖a‖ := IsLawfulAbs.abs_nonneg _
def abs_zero_iff {a: α}: ‖a‖ = 0 ↔ a = 0 := IsLawfulAbs.abs_zero_iff
def abs_mul (a b: α): ‖a * b‖ = ‖a‖ * ‖b‖ := IsLawfulAbs.abs_mul _ _
def abs_add_le_add_abs (a b: α): ‖a + b‖ ≤ ‖a‖ + ‖b‖ := IsLawfulAbs.abs_add_le_add_abs _ _

def abs_zero : ‖(0: α)‖ = 0 := abs_zero_iff.mpr rfl
def of_abs_eq_zero {x: α} : ‖x‖ = 0 -> x = 0 := abs_zero_iff.mp

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
