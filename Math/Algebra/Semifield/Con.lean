import Math.Algebra.Semiring.Con
import Math.Algebra.GroupWithZero.Con
import Math.Algebra.Field.Defs

variable {C α: Type*} [RelLike C α] (c: C)
   [SemifieldOps α] [IsSemifield α] [IsRingCon C]

instance [IsNontrivial (IsCon.Quotient c)] : IsSemifield (IsCon.Quotient c) where
