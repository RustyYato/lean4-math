import Math.Data.FinSupp.Defs
import Math.Algebra.Monoid.Action.Defs
import Math.Algebra.Algebra.Defs

variable [FiniteSupportSet S α]

instance [SemiringOps β] [IsSemiring β] : IsDistribMulAction β (Finsupp α β S) where
  one_smul a := by
    ext i
    apply one_mul
  mul_smul a b c := by
    ext i
    apply mul_assoc
  smul_zero a := by
    ext i
    apply mul_zero
  smul_add a b c := by
    ext i
    apply mul_add
