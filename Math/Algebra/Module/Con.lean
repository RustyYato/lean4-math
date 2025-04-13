import Math.Algebra.Module.Defs
import Math.Algebra.Monoid.Action.Con

variable {C α: Type*} [RelLike C α] (c: C)

instance
  [SemiringOps R] [IsSemiring R]
  [AddMonoidOps α] [IsAddMonoid α] [IsAddCommMagma α]
  [SMul R α] [IsSMulCon C R] [IsAddCon C]
  [IsModule R α] : IsModule R (IsCon.Quotient c) where
  add_smul r s a := by
    induction a with | mk a =>
    apply Quotient.sound
    rw [add_smul]
  zero_smul a := by
    induction a with | mk a =>
    apply Quotient.sound
    rw [zero_smul]
