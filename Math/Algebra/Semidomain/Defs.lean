import Math.Algebra.Dvd

class IsSemidomain (α: Type*) [SemiringOps α] extends IsSemiring α, NoZeroDivisors α, IsNontrivial α, IsCommMagma α where

instance [SemiringOps α] [IsSemiring α] [NoZeroDivisors α] [IsNontrivial α] [IsCommMagma α] : IsSemidomain α where
