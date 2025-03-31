import Math.Algebra.Semiring.Con
import Math.Algebra.AddGroupWithOne.Con
import Math.Algebra.Ring.Defs

variable {C α: Type*} [RelLike C α] (c: C)

instance [RingOps α] [IsRing α] [IsRingCon C] : IsRing (IsCon.Quotient c) := IsRing.inst
