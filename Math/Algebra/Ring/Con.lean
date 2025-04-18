import Math.Algebra.Semiring.Con
import Math.Algebra.AddGroupWithOne.Con
import Math.Algebra.Ring.Defs

variable {C α: Type*} [RelLike C α] (c: C)

variable [RingOps α] [IsRing α] [IsAddCon C] [IsMulCon C]

instance AlgQuotient.instRingOps : RingOps (AlgQuotient c) := inferInstance

instance AlgQuotient.instIsRing : IsRing (AlgQuotient c) := IsRing.inst
