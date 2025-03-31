import Math.Algebra.Monoid.Con
import Math.Algebra.AddMonoidWithOne.Defs

variable {C α: Type*} [RelLike C α] (c: C)

instance [AddMonoidWithOneOps α] [IsAddMonoidWithOne α] [IsAddCon C] : IsAddMonoidWithOne (IsCon.Quotient c) where
    natCast_zero := by
        apply Quotient.sound
        rw [natCast_zero]
    natCast_succ _ := by
        apply Quotient.sound
        rw [natCast_succ]
    ofNat_eq_natCast _ := by
        apply Quotient.sound
        rw [ofNat_eq_natCast]
