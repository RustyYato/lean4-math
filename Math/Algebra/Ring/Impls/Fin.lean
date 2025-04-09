import Math.Algebra.Semiring.Impls.Fin
import Math.Algebra.AddGroupWithOne.Impls.Fin
import Math.Algebra.Ring.Defs

variable (n: ℕ) [NeZero n]

instance Fin.instIsRing : IsRing (Fin n) := IsRing.inst
