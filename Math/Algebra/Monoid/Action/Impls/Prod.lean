import Math.Algebra.Monoid.Impls.Prod
import Math.Algebra.Monoid.Action.Defs

instance [MonoidOps R] [SMul R α] [SMul R β] [IsMonoid R] [IsMulAction R α] [IsMulAction R β] : IsMulAction R (α × β) where
  one_smul := by
    intro a
    ext <;> apply one_smul
  mul_smul := by
    intro r₀ r₁ a
    ext <;> apply mul_smul

instance [MonoidOps R] [SMul R α] [SMul R β] [IsMonoid R]
  [AddMonoidOps α] [AddMonoidOps β] [IsAddMonoid α] [IsAddMonoid β]
  [IsDistribMulAction R α] [IsDistribMulAction R β] : IsDistribMulAction R (α × β) where
  smul_zero := by
    intro a; ext <;> apply smul_zero
  smul_add := by
    intro r a b; ext <;> apply smul_add
