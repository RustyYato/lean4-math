import Math.CategoryTheory.Impls.Alg

namespace Category

structure CommAlg.{u, v} (R: Type v) [SemiringOps R] [IsSemiring R] extends Alg.{u, v} R where
  comm: IsCommMagma A

variable [SemiringOps R] [IsSemiring R]

@[coe]
def CommAlg.toType (a: CommAlg R) : Type _ := a.A

instance : CoeSort (CommAlg.{u, v} R) (Type u) where
  coe := CommAlg.toType

section Impls

variable (a: CommAlg R)

instance : SemiringOps a := a.ops
instance : IsSemiring a := a.semi
instance : SMul R a := a.smul
instance : AlgebraMap R a := a.map
instance : IsAlgebra R a := a.alg
instance : IsCommMagma a := a.comm

end Impls

instance : Category (CommAlg R) where
  Hom A B := A →ₐ[R] B
  id _ := AlgHom.id _
  comp := AlgHom.comp

end Category
