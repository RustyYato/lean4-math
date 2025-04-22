import Math.Algebra.Semiring.Impls.Fin
import Math.Algebra.GroupWithZero.Impls.Fin
import Math.Algebra.Semifield.Defs

instance [Nat.IsPrimeClass n] : IsSemifield (Fin n) := inferInstance
