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

variable [EmbeddingLike F α β]

variable [SemifieldOps β] [IsSemifield β]
  [IsZeroHom F α β] [IsOneHom F α β]
  [IsAddHom F α β] [IsMulHom F α β]

namespace Subsemifield

def preimage (f: F) (s: Subsemifield β) : Subsemifield α := {
  s.toSubgroupWithZero.preimage f, s.toAddSubmonoidWithOne.preimage f with
}

def image (f: F) (s: Subsemifield α) : Subsemifield β := {
  s.toSubgroupWithZero.image f, s.toAddSubmonoidWithOne.image f with
}

def range (f: F) : Subsemifield β := {
  SubgroupWithZero.range f, AddSubmonoidWithOne.range f with
}

end Subsemifield
