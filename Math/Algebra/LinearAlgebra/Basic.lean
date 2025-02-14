import Math.Algebra.LinearMap
import Math.Algebra.Field.Defs

structure VectorSpace (R A: Type*) where
  [smul: SMul R A]
  [scalar_field_ops: FieldOps R]
  [scalar_field: IsField R]
  [vector_add_group_ops: AddGroupOps A]
  [vector_add_group: IsAddGroup A]
  [vector_add_comm: IsAddCommMagma A]
  [is_module: IsModule R A]

namespace VectorSpace

def Scalar (_: VectorSpace R A) := R
def Vector (_: VectorSpace R A) := A

section

variable (V: VectorSpace R A)

instance : FieldOps V.Scalar := V.scalar_field_ops
instance : IsField V.Scalar := V.scalar_field
instance : AddGroupOps V.Vector := V.vector_add_group_ops
instance : IsAddGroup V.Vector := V.vector_add_group
instance : IsAddCommMagma V.Vector := V.vector_add_comm
instance : SMul V.Scalar V.Vector := V.smul
instance : IsModule V.Scalar V.Vector := V.is_module

end

end VectorSpace
