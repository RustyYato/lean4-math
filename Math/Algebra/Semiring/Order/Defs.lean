import Math.Algebra.Monoid.Order.Defs
import Math.Algebra.Semiring.Defs

class IsOrderedNonUnitalNonAssocSemiring (α: Type*)
  [AddMonoidOps α] [Mul α] [LT α] [LE α] extends IsNonUnitalNonAssocSemiring α, IsOrderedAddCommMonoid α where
  mul_nonneg: ∀a b: α, 0 ≤ a -> 0 ≤ b -> 0 ≤ a * b
  mul_le_mul_of_nonneg_left: ∀a b: α, a ≤ b -> ∀c, 0 ≤ c -> c * a ≤ c * b
  mul_le_mul_of_nonneg_right: ∀a b: α, a ≤ b -> ∀c, 0 ≤ c -> a * c ≤ b * c

class IsOrderedSemiring (α: Type*) [SemiringOps α] [LT α] [LE α] extends IsSemiring α, IsOrderedNonUnitalNonAssocSemiring α, IsZeroLeOne α where

instance [SemiringOps α] [LT α] [LE α]
  [hs: IsSemiring α] [ho: IsOrderedNonUnitalNonAssocSemiring α] [IsZeroLeOne α]
  : IsOrderedSemiring α := { hs, ho with }

class IsStrictOrderedNonUnitalNonAssocSemiring (α: Type*)
  [AddMonoidOps α] [Mul α] [LT α] [LE α] extends IsOrderedNonUnitalNonAssocSemiring α where
  mul_pos: ∀a b: α, 0 < a -> 0 < b -> 0 < a * b

class IsStrictOrderedSemiring (α: Type*) [SemiringOps α] [LT α] [LE α] extends
  IsOrderedSemiring α, IsStrictOrderedNonUnitalNonAssocSemiring α where

instance [SemiringOps α] [LT α] [LE α]
  [hs: IsOrderedSemiring α] [ho: IsStrictOrderedNonUnitalNonAssocSemiring α]
  : IsStrictOrderedSemiring α := { hs, ho with }
