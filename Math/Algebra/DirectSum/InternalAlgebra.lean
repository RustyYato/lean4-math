import Math.Algebra.DirectSum.Internal
import Math.Algebra.DirectSum.Algebra
import Math.Algebra.Module.SetLike.Basic

namespace SetLike

variable {γ σ α: Type*} [SetLike σ α] (R: Type*) (A: γ -> σ)

section

variable [SemiringOps R] [SemiringOps α] [AlgebraMap R α] [SMul R α]
  [IsSemiring R] [IsSemiring α] [IsAlgebra R α]

class IsGradedAlgebraMap [Zero γ]  where
  mem_algebraMap (r: R) : (algebraMap r: α) ∈ A 0

instance [Zero γ] [IsGradedAlgebraMap R A] [IsAddSubmonoid σ] : GAlgebraMap R (A ·) where
  toFun := {
    toFun r := ⟨algebraMap r, IsGradedAlgebraMap.mem_algebraMap _⟩
    map_zero := by congr; rw [map_zero]
    map_add {a b} := by
      apply Subtype.val_inj
      simp
      rw [map_add]
  }

instance [AddMonoidOps γ] [IsAddMonoid γ]
  [IsGradedAlgebraMap R A] [IsSubmodule σ R]
  [GradedOne A] [GradedMul A]
  : SMul R (A i) where
  smul r a := ⟨r • a.val, by
    apply mem_smul
    exact a.property⟩

instance [AddMonoidOps γ] [IsAddMonoid γ]
  [IsGradedAlgebraMap R A] [IsSubmodule σ R]
  [GradedOne A] [GradedMul A]
  : IsGAlgebra R (A ·) where
  map_one := by
    apply Subtype.val_inj
    apply map_one
  map_mul {a b} := by
    ext; symm; apply add_zero
    apply map_mul algebraMap
  commutes := by
    intro i r a
    ext; apply add_comm 0
    apply commutes
  smul_def := by
    intro i r a
    ext; symm; apply zero_add
    apply smul_def

end

end SetLike
