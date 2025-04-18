import Math.Algebra.Monoid.Con
import Math.Algebra.AddMonoidWithOne.Defs

variable {C α: Type*} [RelLike C α] (c: C)

instance AlgQuotient.instIsAddMonoidWithOne [AddMonoidWithOneOps α] [IsAddMonoidWithOne α] [IsAddCon C] : IsAddMonoidWithOne (AlgQuotient c) where
    natCast_zero := by
        apply Quotient.sound
        rw [natCast_zero]
    natCast_succ _ := by
        apply Quotient.sound
        rw [natCast_succ]
