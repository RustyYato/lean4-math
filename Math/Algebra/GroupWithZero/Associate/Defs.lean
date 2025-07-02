import Math.Algebra.Monoid.Associate.Defs
import Math.Algebra.GroupWithZero.Con

instance [GroupWithZeroOps α] [IsGroupWithZero α] [IsCommMagma α] : IsNontrivial (AlgQuotient (Associates.Con α)) := inferInstanceAs (IsNontrivial (Associates _))
instance [GroupWithZeroOps α] [IsGroupWithZero α] [IsCommMagma α] : GroupWithZeroOps (Associates α) := inferInstanceAs (GroupWithZeroOps (AlgQuotient _))
instance [GroupWithZeroOps α] [IsGroupWithZero α] [IsCommMagma α] : IsGroupWithZero (Associates α) := inferInstanceAs (IsGroupWithZero (AlgQuotient _))
