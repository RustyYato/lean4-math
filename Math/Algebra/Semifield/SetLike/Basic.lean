import Math.Algebra.Semifield.SetLike.Defs
import Math.Algebra.GroupWithZero.SetLike.Basic
import Math.Algebra.Semiring.SetLike.Basic
import Math.Algebra.Semifield.Defs

variable [SetLike S α] [SemifieldOps α] [IsSemifield α] [IsSubsemifield S] (s: S)

instance : SemifieldOps s := inferInstance
instance : IsSemifield s := inferInstance

instance (s: Subsemifield α) : SemifieldOps s := inferInstance
instance (s: Subsemifield α) : IsSemifield s := inferInstance
instance (s: Subsemifield α) : IsSemiring s := inferInstance
instance (s: Subsemifield α) : IsSemiring s := inferInstance
