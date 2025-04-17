import Math.CategoryTheory.Impls.Alg
import Math.CategoryTheory.Functor.Basic

namespace Category

structure CommAlg.{u, v} (R: Type v) [SemiringOps R] [IsSemiring R] extends Alg.{u, v} R where
  comm: IsCommMagma A

section

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

end

variable (R: Type v) [SemiringOps R] [IsSemiring R]

-- the forgetful functor, a faithful functor from `CommAlg` to `Set`
-- which just gets the underlying set

def CommAlg.toSet : CommAlg.{u, v} R ⥤ Type u where
  obj a := a.A
  map {A B} f :=
    have f: A →ₐ[R] B  := f
    have f: A -> B  := f
    f

instance CommAlg.toSet_faithful : (CommAlg.toSet R).IsFaithful where
  map_inj {A B x y h} := by
    apply DFunLike.coe_inj (F := A →ₐ[R] B)
    assumption

instance : Concrete.{u} (CommAlg.{u, v} R) where
  toSet := CommAlg.toSet R

end Category
