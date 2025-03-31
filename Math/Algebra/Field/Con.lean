import Math.Algebra.Ring.Con
import Math.Algebra.Semifield.Con
import Math.Algebra.Field.Defs

variable {C α: Type*} [RelLike C α] (c: C)
   [FieldOps α] [IsField α] [IsRingCon C]

-- for some reason lean is unable to infer this instance
instance : RingOps (IsCon.Quotient c) := instRingOpsOfSemiringOpsOfNegOfSubOfIntCastOfSMulInt

instance [IsNontrivial (IsCon.Quotient c)] : IsField (IsCon.Quotient c) where
