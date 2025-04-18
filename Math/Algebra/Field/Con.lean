import Math.Algebra.Ring.Con
import Math.Algebra.Semifield.Con
import Math.Algebra.Field.Defs

variable {C α: Type*} [RelLike C α] (c: C)
   [FieldOps α] [IsField α] [IsAddCon C] [IsMulCon C]

instance AlgQuotient.instIsField [IsNontrivial (AlgQuotient c)] : IsField (AlgQuotient c) where
