import Math.Algebra.Semiring.Order.Defs
import Math.Algebra.Ring.Defs
import Math.Ops.Abs

class IsLawfulAbs (α: Type*) {β: Type*}
  [AbsoluteValue α β] [LE β] [LT β]
  [AddGroupOps α] [Mul α]
  [AddMonoidOps β] [Mul β]
  [IsNonUnitalNonAssocRing α]
  [IsOrderedAddCommMonoid β]
  [IsLinearOrder β] where
  abs_nonneg (a: α): 0 ≤ |a|
  abs_zero_iff {a: α}: |a| = 0 ↔ a = 0
  abs_add_le_add_abs (a b: α): |a + b| ≤ |a| + |b|
  abs_neg (a: α): |-a| = |a|
  abs_mul (a b: α): |a * b| = |a| * |b|

variable
  [AbsoluteValue α β] [LE β] [LT β]
  [AddGroupOps α] [Mul α]
  [AddMonoidOps β] [Mul β]
  [IsNonUnitalNonAssocRing α]
  [IsOrderedAddCommMonoid β]
  [IsLinearOrder β] [IsLawfulAbs α]

def abs_nonneg (a: α): 0 ≤ |a| := IsLawfulAbs.abs_nonneg _
def abs_zero_iff {a: α}: |a| = 0 ↔ a = 0 := IsLawfulAbs.abs_zero_iff
def abs_add_le_add_abs (a b: α): |a + b| ≤ |a| + |b| := IsLawfulAbs.abs_add_le_add_abs _ _

def abs_zero : |(0: α)| = 0 := abs_zero_iff.mpr rfl
def of_abs_eq_zero {x: α} : |x| = 0 -> x = 0 := abs_zero_iff.mp

def abs_neg (x: α) : |-x| = |x| := IsLawfulAbs.abs_neg _
def abs_mul (a b: α): |a * b| = |a| * |b| := IsLawfulAbs.abs_mul _ _

def abs_sub_comm (a b: α) : |a - b| = |b - a| := by
  rw [←abs_neg, neg_sub]
