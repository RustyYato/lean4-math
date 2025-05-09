import Math.Algebra.Ring.SetLike.Defs
import Math.Algebra.Semiring.SetLike.Basic
import Math.Algebra.AddGroupWithOne.SetLike.Basic
import Math.Algebra.Ring.Defs

variable [SetLike S α] [RingOps α] [IsSubring S] [IsRing α]
   (s: S)

instance : RingOps s := {
  instSemiringOpsElem s with
}
instance : IsRing s := IsRing.inst

instance (s: Subring α) : RingOps s := inferInstance
instance (s: Subring α) : IsRing s := inferInstance

variable [FunLike F α β]

variable [RingOps β] [IsRing β]
  [IsRingHom F α β]

namespace Subring

def preimage (f: F) (s: Subring β) : Subring α := {
  s.toSubmonoid.preimage f, s.toAddSubgroupWithOne.preimage f with
}

def image (f: F) (s: Subring α) : Subring β := {
  s.toSubmonoid.image f, s.toAddSubgroupWithOne.image f with
}

def range (f: F) : Subring β := {
  Submonoid.range f, AddSubgroupWithOne.range f with
}

end Subring
