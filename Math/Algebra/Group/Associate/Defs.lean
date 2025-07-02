import Math.Algebra.Monoid.Associate.Defs
import Math.Algebra.Group.Con

variable [GroupOps α] [IsGroup α] [IsCommMagma α]

instance : GroupOps (Associates α) := inferInstanceAs (GroupOps (AlgQuotient _))
instance : IsGroup (Associates α) := inferInstanceAs (IsGroup (AlgQuotient _))
