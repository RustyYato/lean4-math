import Math.Algebra.AddMonoidWithOne.Impls.Pi
import Math.Algebra.Semiring.Defs

section Pi

variable {ι: Type*} {α: ι -> Type*}

instance [∀i, Add (α i)] [∀i, Mul (α i)] [∀i, IsLeftDistrib (α i)] : IsLeftDistrib (∀i, α i) where
  mul_add := by
    intro k a b; ext i
    apply mul_add

instance [∀i, Add (α i)] [∀i, Mul (α i)] [∀i, IsRightDistrib (α i)] : IsRightDistrib (∀i, α i) where
  add_mul := by
    intro k a b; ext i
    apply add_mul

instance [∀i, SemiringOps (α i)] [∀i, IsSemiring (α i)] : IsSemiring (∀i, α i) := IsSemiring.inst

end Pi

section Function

variable {ι: Type*} {α: Type*}

instance [Add α] [Mul α] [IsLeftDistrib α] : IsLeftDistrib (ι -> α) :=
  inferInstance
instance [Add α] [Mul α] [IsRightDistrib α] : IsRightDistrib (ι -> α) :=
  inferInstance
instance [SemiringOps α] [IsSemiring α] : IsSemiring (ι -> α) := inferInstance

end Function
