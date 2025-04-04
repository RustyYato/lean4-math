import Math.Algebra.LinearAlgebra.Basic
import Math.CategoryTheory.Basic
import Math.Algebra.Module.LinearMap.Defs

namespace Category

structure Vec.{v, s} (R: Type s) [FieldOps R] [IsField R] where
  Vector: Type v
  [smul: SMul R Vector]
  [vector_add_group_ops: AddGroupOps Vector]
  [vector_add_group: IsAddGroup Vector]
  [vector_add_comm: IsAddCommMagma Vector]
  [is_module: IsModule R Vector]

namespace Vec

variable [FieldOps R] [IsField R] (V: Vec R)

attribute [coe] Vec.Vector
instance : CoeSort (Vec R) (Type u) := ⟨Vec.Vector⟩

instance : AddGroupOps V := V.vector_add_group_ops
instance : IsAddGroup V := V.vector_add_group
instance : IsAddCommMagma V := V.vector_add_comm
instance : SMul R V := V.smul
instance : IsModule R V := V.is_module

end Vec

-- the category of vector spaces, with R-linear maps as homomorphisms
instance [FieldOps R] [IsField R] : Category (Vec R) where
  Hom A B := A →ₗ[R] B
  id _ := LinearMap.id _
  comp := LinearMap.comp

end Category
