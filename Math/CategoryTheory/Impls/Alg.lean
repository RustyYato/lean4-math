import Math.Algebra.Algebra.Hom
import Math.CategoryTheory.Basic

namespace Category

structure Alg.{u, v} (R: Type v) [SemiringOps R] [IsSemiring R] where
  A: Type u
  ops: SemiringOps A := by infer_instance
  semi: IsSemiring A := by infer_instance
  smul: SMul R A := by infer_instance
  map: AlgebraMap R A := by infer_instance
  alg: IsAlgebra R A := by infer_instance

attribute [coe] Alg.A

variable [SemiringOps R] [IsSemiring R]

instance : CoeSort (Alg.{u, v} R) (Type u) where
  coe := Alg.A

section Impls

variable (a: Alg R)

instance : SemiringOps a := a.ops
instance : IsSemiring a := a.semi
instance : SMul R a := a.smul
instance : AlgebraMap R a := a.map
instance : IsAlgebra R a := a.alg

end Impls

instance : Category (Alg R) where
  Hom A B := A →ₐ[R] B
  id _ := AlgHom.id _
  comp := AlgHom.comp

end Category
