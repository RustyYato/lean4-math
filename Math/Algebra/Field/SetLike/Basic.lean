import Math.Algebra.Field.SetLike.Defs
import Math.Algebra.GroupWithZero.SetLike.Basic
import Math.Algebra.Ring.SetLike.Basic
import Math.Algebra.Field.Defs

variable [SetLike S α] [FieldOps α] [IsField α] [IsSubfield S] (s: S)

instance : IsField s := inferInstance
