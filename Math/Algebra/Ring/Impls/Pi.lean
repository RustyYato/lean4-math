import Math.Algebra.Semiring.Impls.Pi
import Math.Algebra.AddGroupWithOne.Impls.Pi
import Math.Algebra.Ring.Defs

section Pi

variable {ι: Type*} {α: ι -> Type*}

instance [∀i, RingOps (α i)] [∀i, IsRing (α i)] : IsRing (∀i, α i) := IsRing.inst

end Pi

section Function

variable {ι: Type*} {α: Type*}

instance [RingOps α] [IsRing α] : IsRing (ι -> α) := inferInstance

end Function
