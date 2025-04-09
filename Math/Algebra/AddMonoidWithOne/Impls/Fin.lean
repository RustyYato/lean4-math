import Math.Algebra.Monoid.Impls.Fin
import Math.Algebra.AddMonoidWithOne.Defs

variable (n: ℕ) [NeZero n]

instance : NatCast (Fin n) where
  natCast := Fin.ofNat' _

instance Fin.instIsAddMonoidWithOne : IsAddMonoidWithOne (Fin n) where
  natCast_zero := rfl
  natCast_succ := by
    intro a
    show Fin.mk _ _ = Fin.mk _ _
    simp
