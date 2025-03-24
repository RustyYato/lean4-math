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

instance : IsStrictOrderedSemiring Nat where
  zero_le_one := Nat.zero_le 1
  add_le_add_left _ _ := Nat.add_le_add_left
  mul_pos := by apply Nat.mul_pos
  mul_nonneg := by exact fun a b a_1 a_2 => Nat.zero_le _
  mul_le_mul_of_nonneg_left := fun a b a_1 c a_2 => Nat.mul_le_mul_left c a_1
  mul_le_mul_of_nonneg_right := fun a b a_1 c a_2 => Nat.mul_le_mul_right c a_1

instance : IsStrictOrderedSemiring Int where
  zero_le_one := by exact Int.zero_le_ofNat 1
  add_le_add_left _ _ := Int.add_le_add_left
  mul_pos := by apply Int.mul_pos
  mul_nonneg := by exact fun a b a_1 a_2 => Int.mul_nonneg a_1 a_2
  mul_le_mul_of_nonneg_left := fun a b a_1 c a_2 => Int.mul_le_mul_of_nonneg_left a_1 a_2
  mul_le_mul_of_nonneg_right := fun a b a_1 c a_2 => by exact Int.mul_le_mul_of_nonneg_right a_1 a_2

section

variable [AddMonoidOps α] [Mul α] [LT α] [LE α] [IsOrderedNonUnitalNonAssocSemiring α]

def mul_nonneg: ∀a b: α, 0 ≤ a -> 0 ≤ b -> 0 ≤ a * b := IsOrderedNonUnitalNonAssocSemiring.mul_nonneg
def mul_le_mul_of_nonneg_left: ∀a b: α, a ≤ b -> ∀c, 0 ≤ c -> c * a ≤ c * b := IsOrderedNonUnitalNonAssocSemiring.mul_le_mul_of_nonneg_left
def mul_le_mul_of_nonneg_right: ∀a b: α, a ≤ b -> ∀c, 0 ≤ c -> a * c ≤ b * c := IsOrderedNonUnitalNonAssocSemiring.mul_le_mul_of_nonneg_right

end

section

variable [AddMonoidOps α] [Mul α] [LT α] [LE α] [IsStrictOrderedNonUnitalNonAssocSemiring α]

def mul_pos: ∀a b: α, 0 < a -> 0 < b -> 0 < a * b := IsStrictOrderedNonUnitalNonAssocSemiring.mul_pos

end

section

variable [SemiringOps α] [LE α] [LT α] [IsStrictOrderedSemiring α]
  [IsNontrivial α]

def two_pos : 0 < (2: α) := by
  show (0: α) < OfNat.ofNat (0 + 2)
  have := ofNat_eq_natCast (α := α) 0
  rw [ofNat_eq_natCast (α := α) 0, Nat.zero_add, show 2 = 1 + 1 by rfl, natCast_add]
  apply lt_of_lt_of_le
  apply zero_lt_one
  rw [←add_zero (1: α), natCast_one]
  apply add_le_add_left
  apply zero_le_one

end

instance [SemiringOps α] [LT α] [LE α] [IsOrderedSemiring α]
  : IsOrderedAddCommMonoid α := inferInstance
