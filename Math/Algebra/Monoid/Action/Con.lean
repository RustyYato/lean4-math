import Math.Algebra.Monoid.Con
import Math.Algebra.Monoid.Action.Defs

variable {C α: Type*} [RelLike C α] (c: C) [MonoidOps R] [IsMonoid R]

instance AlgQuotient.instIsMulAction [SMul R α] [IsSMulCon C R] [IsMulAction R α] : IsMulAction R (AlgQuotient c) where
  one_smul a := by
    induction a with | mk a =>
    apply Quotient.sound
    rw [one_smul]
  mul_smul _ _ a := by
    induction a with | mk a =>
    apply Quotient.sound
    rw [mul_smul]

instance AlgQuotient.instIsDistribMulAction [SMul R α] [IsSMulCon C R] [AddMonoidOps α] [IsAddMonoid α] [IsAddCon C] [IsDistribMulAction R α] : IsDistribMulAction R (AlgQuotient c) where
  smul_zero r := by
    apply Quotient.sound
    rw [smul_zero]
  smul_add r a b := by
    induction a with | mk a =>
    induction b with | mk b =>
    apply Quotient.sound
    rw [smul_add]
