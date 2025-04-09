import Math.Algebra.Semifield.Impls.Fin
import Math.Algebra.Ring.Impls.Fin
import Math.Algebra.Field.Defs

instance [Fact (Nat.IsPrime n)] : IsField (Fin n) := inferInstance
