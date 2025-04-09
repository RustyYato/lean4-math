import Math.Algebra.Monoid.Impls.Pi
import Math.Algebra.AddMonoidWithOne.Defs

section Pi

variable {ι: Type*} {α: ι -> Type*}

instance [∀i, AddMonoidWithOneOps (α i)] [∀i, IsAddMonoidWithOne (α i)] : IsAddMonoidWithOne (∀i, α i) where
  natCast_zero := by ext i; apply natCast_zero
  natCast_succ := by intro n; ext i; apply natCast_succ

end Pi

section Function

variable {ι: Type*} {α: Type*}

instance [AddMonoidWithOneOps α] [IsAddMonoidWithOne α] : IsAddMonoidWithOne (ι -> α) :=
  inferInstance

end Function
