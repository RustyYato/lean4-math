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

variable [SMul R A] [SMul R B]
  [IsSemiring R] [IsSemiring A] [IsSemiring B]
  [IsAlgebra R A] [IsAlgebra R B]

def AlgEquiv.congrHomMulOpp : (A →ₐ[R] B) ≃ (Aᵐᵒᵖ →ₐ[R] Bᵐᵒᵖ) where
  toFun f := {
    toFun a := MulOpp.mk (f a.get)
    map_add := by simp [map_add]
    map_mul := by simp [map_mul]
    map_algebraMap r := by
      show MulOpp.mk (f (algebraMap r: A)) = MulOpp.mk (algebraMap r: B)
      rw [map_algebraMap]
  }
  invFun f := {
    toFun a := (f (MulOpp.mk a)).get
    map_add := by simp [map_add]
    map_mul := by simp [map_mul]
    map_algebraMap r := by
      show (f (algebraMap r)).get = _
      rw [map_algebraMap]
      rfl
  }
  leftInv _ := rfl
  rightInv _ := rfl

def AlgEquiv.mulopp_hom_eqv_hom_mul_opp : (Aᵐᵒᵖ →ₐ[R] B) ≃ (A →ₐ[R] Bᵐᵒᵖ) :=
  AlgEquiv.congrHomMulOpp (A := Aᵐᵒᵖ) (B := B)

@[simp] def AlgHom.toLinearMap_eq_coe (f: A →ₐ[R] B) : (f.toLinearMap: _ -> _) = f := rfl
@[simp] def AlgEquiv.toAlgHom_eq_coe (f: A ≃ₐ[R] B) : (f.toAlgHom: _ -> _) = f := rfl

end
