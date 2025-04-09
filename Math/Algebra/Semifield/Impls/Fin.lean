import Math.Algebra.Semiring.Impls.Fin
import Math.Algebra.GroupWithZero.Impls.Fin
import Math.Algebra.Semifield.Defs

instance [Fact (Nat.IsPrime n)] : IsSemifield (Fin n) := inferInstance
