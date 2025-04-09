import Math.Algebra.Monoid.Impls.Pi
import Math.Algebra.Monoid.Action.Defs

section Pi

variable {ι: Type*} {α: ι -> Type*}

instance [MonoidOps R] [∀i, SMul R (α i)] [IsMonoid R] [∀i, IsMulAction R (α i)] : IsMulAction R (∀i, α i) where
  one_smul := by
    intro a
    ext i; apply one_smul
  mul_smul := by
    intro r₀ r₁ a
    ext i; apply mul_smul

instance [MonoidOps R] [∀i, SMul R (α i)] [IsMonoid R]
  [∀i, AddMonoidOps (α i)] [∀i, IsAddMonoid (α i)]
  [∀i, IsDistribMulAction R (α i)] : IsDistribMulAction R (∀i, α i) where
  smul_zero := by
    intro a; ext i; apply smul_zero
  smul_add := by
    intro r a b; ext i; apply smul_add

end Pi

section Function

variable {ι α: Type*}

instance [MonoidOps R] [SMul R α] [IsMonoid R] [IsMulAction R α] : IsMulAction R (ι -> α) := inferInstance
instance [MonoidOps R] [SMul R α] [IsMonoid R]
  [AddMonoidOps α] [IsAddMonoid α]
  [IsDistribMulAction R α] : IsDistribMulAction R (ι -> α) := inferInstance

end Function
