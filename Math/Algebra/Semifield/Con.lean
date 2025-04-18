import Math.Algebra.Semiring.Con
import Math.Algebra.GroupWithZero.Con
import Math.Algebra.Field.Defs

variable {C α: Type*} [RelLike C α] (c: C)
   [SemifieldOps α] [IsSemifield α] [IsRingCon C]

open Classical

instance AlgQuotient.instIsSemifield [IsNontrivial (AlgQuotient c)] : IsSemifield (AlgQuotient c) where
