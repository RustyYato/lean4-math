import Math.Algebra.Module.SetLike.Basic
import Math.Algebra.GradedRing.Defs
import Math.Algebra.DirectSum.InternalAlgebra

variable
  [AddMonoidOps γ] [IsAddMonoid γ]
  [SemiringOps α] [IsSemiring α]
  [SemiringOps R] [IsSemiring R]
  [SMul R α] [DecidableEq γ]
  (A: γ -> Submodule R α)
  [SetLike.GradedOne A] [SetLike.GradedMul A]
  [dec: DirectSum.Decomposition A]

abbrev IsGradedAlgebra := IsGradedRing A

private instance : One (A 0) := DirectSum.instOneOfNat (A := (A ·))
private instance : Mul (A 0) := DirectSum.instMulOfNat (A := (A ·))

variable [IsGradedAlgebra A]
  [AlgebraMap R α] [SetLike.IsGradedAlgebraMap R A]
  [IsAlgebra R α]

def decomposeAlg : α ≃ₐ[R] ⊕i, A i := {
  decomposeRing _ with
  map_algebraMap r := by
    show decomposeRing A (algebraMap r) = algebraMap r
    conv => {
      rhs; rw [algebraMap, AlgebraMap.toRingHom, DirectSum.instAlgebraMapOfGAlgebraMap,
        AlgebraMap.ofHom]
    }
    simp
    show _ = DirectSum.ι 0 _
    apply (decomposeRing _).symm.inj
    simp
    show _ = (decompose dec).symm _
    rw [DirectSum.Decomposition.symm_apply_decompose, DirectSum.get_ι]
    rfl
}
