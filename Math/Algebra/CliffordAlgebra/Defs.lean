import Math.Algebra.TensorAlgebra.Basic
import Math.Algebra.QuadraticForm.Basic

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

section ι

variable [SemiringOps R] [IsSemiring R] [IsCommMagma R] [AddMonoidOps V]
  [IsAddMonoid V] [IsAddCommMagma V] [SMul R V] [IsModule R V]

variable (Q: QuadraticForm R V)

namespace CliffordAlgebra

def ι : V →ₗ[R] CliffordAlgebra Q :=
  (RingQuot.mkAlgHom R _).toLinearMap.comp (TensorAlgebra.ι R)

private def algmap_coe_eq
  [SemiringOps A] [SemiringOps B] [AlgebraMap R A] [AlgebraMap R B]
  (f: A →ₐ[R] B) (x: A) : f.toFun x = f x := rfl

/-- As well as being linear, `ι Q` squares to the quadratic form -/
@[simp]
theorem ι_sq_scalar (v: V) : ι Q v * ι Q v = algebraMap (Q v) := by
  rw [ι]
  dsimp [LinearMap.comp, DFunLike.coe, AlgHom.toLinearMap]
  rw [algmap_coe_eq, ←resp_mul (f := RingQuot.mkAlgHom R (CliffordAlgebra.Rel Q))]
  show _ = algebraMap _
  apply (RingQuot.mkAlgHom_rel R (CliffordAlgebra.Rel.intro v)).trans
  apply resp_algebraMap

end CliffordAlgebra

-- the canonical map from a TensorAlgebra to a CliffordAlgebra
def toClifford : TensorAlgebra R V →ₐ[R] CliffordAlgebra Q :=
  TensorAlgebra.lift R (CliffordAlgebra.ι Q)

@[simp]
theorem toClifford_ι (v: V) : toClifford Q (TensorAlgebra.ι R v) = CliffordAlgebra.ι Q v := by
  simp [toClifford]

end ι
