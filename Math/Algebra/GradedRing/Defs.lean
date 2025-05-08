import Math.Algebra.DirectSum.Internal
import Math.Algebra.DirectSum.Decomposition

variable
  [AddMonoidOps γ] [IsAddMonoid γ]
  [SemiringOps α] [IsSemiring α]
  [SetLike σ α] [DecidableEq γ]
  [IsAddSubmonoid σ] (A: γ -> σ)

class IsGradedRing [DirectSum.Decomposition A] : Prop extends SetLike.GradedMul A, SetLike.GradedOne A where

variable [dec: DirectSum.Decomposition A] [IsGradedRing A]

def decomposeRing : α ≃+* ⊕i, A i := {
  decompose dec with
  map_one := by
    show decompose dec 1 = 1
    apply (decompose dec).symm.inj
    simp; symm
    rw [dec.symm_apply_decompose, DirectSum.one_eq, DirectSum.get_ι]
    rfl
  map_mul := by
    intro a b
    show decompose dec (a * b) = decompose dec a * decompose dec b
    apply (decompose dec).symm.inj
    simp; symm
    simp [DirectSum.Decomposition.symm_apply_decompose, DirectSum.get_ι]
    rw [DirectSum.get, DirectSum.apply_lift_eq_apply_liftRing]
    rw [map_mul, ←DirectSum.apply_lift_eq_apply_liftRing, ←DirectSum.apply_lift_eq_apply_liftRing]
    show DirectSum.get (decompose dec a) * DirectSum.get (decompose dec b) = _
    simp [←DirectSum.Decomposition.symm_apply_decompose]
    all_goals intros; rfl
}
