import Math.Algebra.Ring.Defs
import Math.Algebra.Semifield.Defs

class FieldOps (α: Type*) extends RingOps α, SemifieldOps α where

instance (priority := 50) [RingOps α] [CheckedIntPow? α] [CheckedInv? α] [CheckedDiv? α] : FieldOps α where

class IsNonCommField (α: Type*) [FieldOps α] : Prop extends IsRing α, IsNonCommSemifield α where
class IsField (α: Type*) [FieldOps α] : Prop extends IsNonCommField α, IsSemifield α  where

instance [FieldOps α] [h: IsRing α] [g: IsGroupWithZero α] : IsNonCommField α := { h, g with }
instance [FieldOps α] [IsNonCommField α] [IsCommMagma α] : IsField α := {  }
