import Math.Algebra.Semiring.SetLike.Defs
import Math.Algebra.AddMonoidWithOne.SetLike.Basic
import Math.Algebra.Semiring.Defs

variable [SetLike S α] [SemiringOps α] [IsSubsemiring S] [IsSemiring α]
   (s: S)

instance : SemiringOps s := inferInstance

instance : IsSemiring s := {
  instIsMonoidElem s with
  mul_add k a b := by
    apply Subtype.val_inj
    apply mul_add
  add_mul a b k := by
    apply Subtype.val_inj
    apply add_mul
}

variable [FunLike F α β]

variable [SemiringOps β] [IsSemiring β]
  [IsZeroHom F α β] [IsOneHom F α β]
  [IsAddHom F α β] [IsMulHom F α β]

namespace Subsemiring

def preimage (f: F) (s: Subsemiring β) : Subsemiring α := {
  s.toSubmonoid.preimage f, s.toAddSubmonoidWithOne.preimage f with
}

def image (f: F) (s: Subsemiring α) : Subsemiring β := {
  s.toSubmonoid.image f, s.toAddSubmonoidWithOne.image f with
}

def range (f: F) : Subsemiring β := {
  Submonoid.range f, AddSubmonoidWithOne.range f with
}

end Subsemiring
