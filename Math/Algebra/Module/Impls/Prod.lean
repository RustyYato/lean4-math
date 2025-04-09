import Math.Algebra.Monoid.Action.Impls.Prod
import Math.Algebra.Module.Defs

instance [SemiringOps R] [SMul R α] [SMul R β] [IsSemiring R]
  [AddMonoidOps α] [AddMonoidOps β] [IsAddMonoid α] [IsAddMonoid β]
  [IsAddCommMagma α] [IsAddCommMagma β]
  [IsModule R α] [IsModule R β] : IsModule R (α × β) where
  add_smul := by
    intro r s a
    ext <;> apply add_smul
  zero_smul := by
    intro r
    ext <;> apply zero_smul
