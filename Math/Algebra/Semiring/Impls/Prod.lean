import Math.Algebra.AddMonoidWithOne.Impls.Prod
import Math.Algebra.Semiring.Defs

instance [Add α] [Add β] [Mul α] [Mul β] [IsLeftDistrib α] [IsLeftDistrib β] : IsLeftDistrib (α × β) where
  mul_add := by
    intro k a b; ext <;>
    apply mul_add

instance [Add α] [Add β] [Mul α] [Mul β] [IsRightDistrib α] [IsRightDistrib β] : IsRightDistrib (α × β) where
  add_mul := by
    intro k a b; ext <;>
    apply add_mul

instance [SemiringOps α] [SemiringOps β] : SemiringOps (α × β) := inferInstance

instance [SemiringOps α] [SemiringOps β] [h: IsSemiring α] [g: IsSemiring β] : IsSemiring (α × β) := IsSemiring.inst
