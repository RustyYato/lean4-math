import Math.Algebra.Monoid.Order.Defs
import Math.Algebra.GroupWithZero.Defs

section IsOrderedCommMonoid

variable [GroupWithZeroOps α] [IsGroupWithZero α] [LT α] [LE α] [IsOrderedCommMonoid α]

def le_of_mul_le_mul_left₀ : ∀a b c: α, c ≠ 0 -> c * a ≤ c * b -> a ≤ b := by
  intro a b c hc h
  have := mul_le_mul_left _ _ h c⁻¹?
  rwa [←mul_assoc, ←mul_assoc, inv?_mul_cancel, one_mul, one_mul] at this

def le_of_mul_le_mul_right₀ : ∀a b c: α, c ≠ 0 -> a * c ≤ b * c -> a ≤ b := by
  intro a b c hc h
  have := mul_le_mul_right _ _ h c⁻¹?
  rwa [mul_assoc, mul_assoc, mul_inv?_cancel, mul_one, mul_one] at this

end IsOrderedCommMonoid
