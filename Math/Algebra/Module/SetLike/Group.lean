import Math.Algebra.Group.SetLike.Defs
import Math.Algebra.Module.SetLike.Defs
import Math.Algebra.Group.Defs
import Math.Algebra.Module.Defs

variable
  [RingOps R] [IsRing R]
  [AddGroupOps M] [IsAddGroup M] [IsAddCommMagma M]
  [SMul R M] [IsModule R M]
  [SetLike S M] [IsSMulMem S R]
  [IsModule R M]

def IsSMulMem.toIsNegMem [SetLike S M] [IsSMulMem S R] : IsNegMem S where
  mem_neg s a h := by
    rw [←one_smul (R := R) a, ←neg_smul]
    apply mem_smul
    assumption

instance : IsNegMem (Submodule R M) := IsSMulMem.toIsNegMem (R := R) (M := M)
