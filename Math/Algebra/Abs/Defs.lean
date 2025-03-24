import Math.Algebra.Semiring.Order.Defs
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
  -- this is a way of hacking in ‖-a‖ = ‖a‖ without relying on negatives
  -- technically this is not an axiom for aboslute values
  -- but it is too tedious to prove normally
  abs_eq_of_add_eq_zero (a b: α) : a + b = 0 -> ‖a‖ = ‖b‖

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
