import Math.Algebra.Semiring.Impls.Prod
import Math.Algebra.AddGroupWithOne.Impls.Prod
import Math.Algebra.Ring.Defs

instance [RingOps α] [RingOps β] : RingOps (α × β) := inferInstance

instance [RingOps α] [RingOps β] [IsRing α] [IsRing β] : IsRing (α × β) := IsRing.inst
