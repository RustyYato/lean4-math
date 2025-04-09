import Math.Algebra.Semigroup.Impls.Prod
import Math.Algebra.Monoid.Defs

instance [AddMonoidOps α] [AddMonoidOps β] [IsAddMonoid α] [IsAddMonoid β] : IsAddMonoid (α × β) where
  zero_nsmul := by
    intro f; ext <;>
    apply zero_nsmul
  succ_nsmul := by
    intro n f; ext <;>
    apply succ_nsmul

instance [MonoidOps α] [MonoidOps β] [IsMonoid α] [IsMonoid β] : IsMonoid (α × β)  :=
  inferInstanceAs (IsMonoid (MulOfAdd (AddOfMul α × AddOfMul β)))
