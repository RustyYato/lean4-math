import Math.Algebra.TensorAlgebra.Basic
import Math.Algebra.QuadraticForm

section

variable [SemiringOps R] [IsSemiring R] [IsCommMagma R] [AddMonoidOps V]
  [IsAddMonoid V] [IsAddCommMagma V] [SMul R V] [IsModule R V]

variable (Q: QuadraticForm R V)

open TensorAlgebra in
inductive CliffordAlgebra.Rel : TensorAlgebra R V -> TensorAlgebra R V -> Prop where
| intro (a: V) : Rel (ι R a * ι R a) (algebraMap (Q a))

def CliffordAlgebra := RingQuot (CliffordAlgebra.Rel Q)

end

section Instances

open CliffordAlgebra

variable [SemiringOps R] [IsSemiring R] [IsCommMagma R] [AddMonoidOps V]
  [IsAddMonoid V] [IsAddCommMagma V] [SMul R V] [IsModule R V]

variable (Q: QuadraticForm R V)

instance : SemiringOps (CliffordAlgebra Q) := RingQuot.instSemiringOps (R := TensorAlgebra R V)
instance : SMul R (CliffordAlgebra Q) := inferInstanceAs (SMul R (RingQuot (Rel Q)))
instance : AlgebraMap R (CliffordAlgebra Q) := inferInstanceAs (AlgebraMap R (RingQuot (Rel Q)))
instance : IsSemiring (CliffordAlgebra Q) := inferInstanceAs (IsSemiring (RingQuot (Rel Q)))
instance : IsAlgebra R (CliffordAlgebra Q) := inferInstanceAs (IsAlgebra R (RingQuot (Rel Q)))

instance : Add (CliffordAlgebra Q) := inferInstance
instance : Mul (CliffordAlgebra Q) := inferInstance

end Instances

section Instances

-- a shortcut instance to prevent timeouts
local instance (priority := 5000) [RingOps α] [IsRing α] : IsSemiring α := IsRing.toIsSemiring

variable [RingOps R] [IsRing R] [IsCommMagma R] [AddGroupOps V]
  [IsAddGroup V] [IsAddCommMagma V] [SMul R V] [IsModule R V]

variable (Q: QuadraticForm R V)

instance : RingOps (CliffordAlgebra Q) := RingQuot.instRingOps
instance : IsRing (CliffordAlgebra Q) := inferInstanceAs (IsRing (RingQuot (CliffordAlgebra.Rel Q)))
instance : Sub (CliffordAlgebra Q) := inferInstance
instance : Neg (CliffordAlgebra Q) := inferInstance

end Instances
