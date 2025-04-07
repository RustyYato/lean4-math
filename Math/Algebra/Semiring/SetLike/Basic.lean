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
