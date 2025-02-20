import Math.Algebra.Ring.SetLike.Defs
import Math.Algebra.Semiring.SetLike.Basic
import Math.Algebra.AddGroupWithOne.SetLike.Basic
import Math.Algebra.Ring.Defs

variable [SetLike S α] [RingOps α] [IsSubRing S] [IsRing α]
   (s: S)

instance : RingOps s := {
  instSemiringOpsElem s with
}
instance : IsRing s := inferInstance
