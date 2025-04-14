import Math.Algebra.Group.Units.Defs
import Math.Algebra.Ring.Defs

instance [RingOps α] [IsRing α] : Neg (Units α) where
  neg a := {
    val := -a.val
    inv := -a.inv
    val_mul_inv := by rw [←neg_mul_left, ←neg_mul_right, neg_neg, a.val_mul_inv]
    inv_mul_val := by rw [←neg_mul_left, ←neg_mul_right, neg_neg, a.inv_mul_val]
  }
