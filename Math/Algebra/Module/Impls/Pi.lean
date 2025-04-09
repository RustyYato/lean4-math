import Math.Algebra.Monoid.Action.Impls.Pi
import Math.Algebra.Module.Defs

section Pi

variable {ι: Type*} {α: ι -> Type*}

instance [SemiringOps R] [∀i, SMul R (α i)] [IsSemiring R]
  [∀i, AddMonoidOps (α i)] [∀i, IsAddMonoid (α i)]
  [∀i, IsAddCommMagma (α i)] [∀i, IsModule R (α i)] : IsModule R (∀i, α i) where
  add_smul := by
    intro r s a
    ext i; apply add_smul
  zero_smul := by
    intro r
    ext i; apply zero_smul

end Pi

section Function

variable {ι α: Type*}

instance [SemiringOps R] [SMul R α] [IsSemiring R]
  [AddMonoidOps α] [IsAddMonoid α]
  [IsAddCommMagma α] [IsModule R α] : IsModule R (ι -> α) := inferInstance

end Function
