import Math.Algebra.Dvd
import Math.Algebra.GroupWithZero.Defs

class IsSemidomain (α: Type*) [SemiringOps α] extends IsSemiring α, NoZeroDivisors α, IsNontrivial α, IsCommMagma α where

instance [SemiringOps α] [IsSemiring α] [NoZeroDivisors α] [IsNontrivial α] [IsCommMagma α] : IsSemidomain α where
