import Math.Algebra.Module.SetLike.Basic
import Math.Algebra.GradedRing.Defs
import Math.Algebra.DirectSum.InternalAlgebra

variable
  [AddMonoidOps γ] [IsAddMonoid γ]
  [SemiringOps α] [IsSemiring α]
  [SemiringOps R] [IsSemiring R]
  [SMul R α] [DecidableEq γ]
  [AlgebraMap R α] [IsAlgebra R α]
  (A: γ -> Submodule R α)
  [SetLike.GradedOne A] [SetLike.GradedMul A]
  [dec: DirectSum.Decomposition A]
  [SetLike.IsGradedAlgebraMap R A]

abbrev IsGradedAlgebra := IsGradedRing A

def decomposeAlg [IsGradedAlgebra A] : α ≃ₐ[R] ⊕i, A i := {
  decomposeRing _ with
  map_algebraMap r := by
    show decomposeRing A (algebraMap r) = algebraMap r
    conv => {
      rhs; rw [algebraMap, AlgebraMap.toRingHom, DirectSum.instAlgebraMapOfGAlgebraMap,
        AlgebraMap.ofHom]
    }
    show _ = DirectSum.ι 0 _
    apply (decomposeRing _).symm.inj
    simp
    show _ = (decompose dec).symm _
    rw [DirectSum.Decomposition.symm_apply_decompose, DirectSum.get_ι]
    rfl
}
