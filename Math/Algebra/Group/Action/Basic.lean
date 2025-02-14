import Math.Algebra.Monoid.Action.Defs
import Math.Algebra.Group.Defs

def smul_neg [SMul R M] [MonoidOps R] [AddGroupOps M] [IsAddGroup M] [IsDistribMulAction R M]
  (r: R) (x: M) : r • -x = -(r • x) := by
  refine neg_eq_of_add_right ?_
  rw [←smul_add, neg_add_cancel, smul_zero]
