import Math.Algebra.AddMonoidWithOne.Impls.Fin
import Math.Algebra.Semiring.Defs

variable (n: ℕ) [NeZero n]

instance Fin.instIsLeftDistrib : IsLeftDistrib (Fin n) where
  mul_add _ _ _ := by
    show Fin.mk _ _ = Fin.mk _ _
    simp only [Nat.add_mod_mod, Nat.mod_add_mod, Fin.mk.injEq]
    rw [Nat.mul_mod, Nat.mod_mod, ←Nat.mul_mod]
    rw [mul_add]

instance Fin.instIsSemiring : IsSemiring (Fin n) := IsSemiring.inst
