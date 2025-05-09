import Math.Algebra.Monoid.Action.Defs
import Math.Algebra.Monoid.Action.SetLike.Defs

variable [SetLike S α] [SMul R α] [IsSMulMem S R] (s: S)

instance : SMul R s where
  smul r a := ⟨r • a.val, mem_smul _ _ a.property⟩
