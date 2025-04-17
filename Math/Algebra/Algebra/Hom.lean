import Math.Algebra.Hom.Defs
import Math.Algebra.Module.LinearMap.Defs
import Math.Algebra.Algebra.Defs
import Math.Logic.Equiv.Like

variable [FunLike F A B] [SMul R A] [SMul R B]

section

variable
  [SemiringOps R] [IsSemiring R]
  [SemiringOps A] [IsSemiring A] [AlgebraMap R A] [IsAlgebra R A]
  [SemiringOps B] [IsSemiring B] [AlgebraMap R B] [IsAlgebra R B]
  [IsMulHom F A B] [IsAlgebraMapHom F R A B]

instance (priority := 1100): IsSMulHom F R A B where
  map_smul := by
    intro f r x
    rw [smul_def, smul_def, map_mul, map_algebraMap]

instance (priority := 2000) AlgHom.instIsSMulHom : IsSMulHom (A →ₐ[R] B) R A B := inferInstance
instance (priority := 2000) AlgEmbedding.instIsSMulHom : IsSMulHom (A ↪ₐ[R] B) R A B := inferInstance
instance (priority := 2000) AlgEquiv.instIsSMulHom : IsSMulHom (A ≃ₐ[R] B) R A B := inferInstance

end

section

variable (F R A B: Type*)
  [FunLike F A B]
  [SemiringOps R] [SemiringOps A] [SemiringOps B] [SemiringOps C]
  [AlgebraMap R A] [AlgebraMap R B] [AlgebraMap R C]

variable [IsAddHom F A B] [IsMulHom F A B] [IsAlgebraMapHom F R A B]
  [SMul R A] [SMul R B] [IsSemiring A] [IsSemiring B] [IsSemiring R] [IsAlgebra R A] [IsAlgebra R B]

def toAlgHom (f: F) : A →ₐ[R] B where
  toFun := f
  map_algebraMap := map_algebraMap f
  map_mul := map_mul f
  map_add := map_add f

end

section

variable {R A B C: Type*}
  [FunLike F A B]
  [SemiringOps R] [SemiringOps A] [SemiringOps B] [SemiringOps C]
  [AlgebraMap R A] [AlgebraMap R B] [AlgebraMap R C]

@[ext]
def AlgHom.ext (f g: A →ₐ[R] B) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _

def AlgHom.toLinearMap
  [SMul R A] [SMul R B]
  [IsSemiring R] [IsSemiring A] [IsSemiring B]
  [IsAlgebra R A] [IsAlgebra R B]
  (h: A →ₐ[R] B) : A →ₗ[R] B := _root_.toLinearMap h

protected def AlgHom.toRingHom (f: A →ₐ[R] B) : A →+* B :=
  toRingHom f

end
