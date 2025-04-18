import Math.Algebra.AddMonoidWithOne.Con
import Math.Algebra.Semiring.Defs

variable {C α: Type*} [RelLike C α] (c: C)

instance AlgQuotient.instIsLeftDistrib [Add α] [Mul α] [IsLeftDistrib α] [IsAddCon C] [IsMulCon C] : IsLeftDistrib (AlgQuotient c) where
  mul_add k a b := by
    induction a; induction b; induction k
    apply Quotient.sound
    rw [mul_add]
instance AlgQuotient.instIsRightDistrib [Add α] [Mul α] [IsRightDistrib α] [IsAddCon C] [IsMulCon C] : IsRightDistrib (AlgQuotient c) where
  add_mul a b k := by
    induction a; induction b; induction k
    apply Quotient.sound
    rw [add_mul]

instance AlgQuotient.instIsSemiring [SemiringOps α] [IsSemiring α] [IsAddCon C] [IsMulCon C] : IsSemiring (AlgQuotient c) := IsSemiring.inst
