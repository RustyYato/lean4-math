import Math.Algebra.Field.SetLike.Defs
import Math.Algebra.GroupWithZero.SetLike.Basic
import Math.Algebra.Ring.SetLike.Basic
import Math.Algebra.Field.Defs

variable [SetLike S α] [FieldOps α] [IsField α] [IsSubfield S] (s: S)

instance : FieldOps s := inferInstance
instance : IsField s := inferInstance

instance (s: Subfield α) : FieldOps s := inferInstance
instance (s: Subfield α) : IsField s := inferInstance
instance (s: Subfield α) : IsRing s := inferInstance
instance (s: Subfield α) : IsSemiring s := inferInstance
