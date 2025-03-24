import Math.Algebra.Order.Abs
import Math.Algebra.Group.Defs

variable
  [AbsoluteValue α β] [LE β] [LT β]
  [AddGroupOps α] [Mul α]
  [AddMonoidOps β] [Mul β]
  [IsNonUnitalNonAssocSemiring α]
  [IsAddGroup α]
  [IsOrderedNonUnitalNonAssocSemiring β]
  [IsLawfulAbs α]

def abs_sub_comm (a b: α) : ‖a - b‖ = ‖-(b - a)‖ := by
  rw [neg_eq_neg_one_zsmul]
  sorry
