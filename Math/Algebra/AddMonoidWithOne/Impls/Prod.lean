import Math.Algebra.Monoid.Impls.Prod
import Math.Algebra.AddMonoidWithOne.Defs

instance [AddMonoidWithOneOps α] [AddMonoidWithOneOps β] [IsAddMonoidWithOne α] [IsAddMonoidWithOne β] : IsAddMonoidWithOne (α × β) where
  natCast_zero := by ext <;> apply natCast_zero
  natCast_succ := by intro n; ext <;> apply natCast_succ
