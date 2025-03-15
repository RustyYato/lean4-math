import Math.Algebra.Monoid.Action.Defs
import Math.Algebra.Group.Defs

def smul_neg [SMul R M] [MonoidOps R] [AddGroupOps M] [IsAddGroup M] [IsMonoid R] [IsDistribMulAction R M]
  (r: R) (x: M) : r • -x = -(r • x) := by
  refine neg_eq_of_add_right ?_
  rw [←smul_add, neg_add_cancel, smul_zero]

def smul_sub [SMul R M] [MonoidOps R] [AddGroupOps M] [IsAddGroup M] [IsMonoid R] [IsDistribMulAction R M]
  (r: R) (a b: M) : r • (a - b) = r • a - r • b := by
  rw [sub_eq_add_neg, sub_eq_add_neg, smul_add, smul_neg]
