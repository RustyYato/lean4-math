import Math.Algebra.Monoid.Order.Defs
import Math.Algebra.Group.Defs

instance [LE α] [LT α] [AddGroupOps α] [IsOrderedAddCommMonoid α] [IsAddGroup α] : IsOrderedCancelAddCommMonoid α where
  le_of_add_le_add_left := by
    intro k a b h
    have := add_le_add_left _ _ h (-k)
    rwa [←add_assoc, ←add_assoc, neg_add_cancel, zero_add, zero_add] at this

instance [LE α] [LT α] [GroupOps α] [IsOrderedCommMonoid α] [IsGroup α] : IsOrderedCancelCommMonoid α where
  le_of_mul_le_mul_left := le_of_add_le_add_left (α := AddOfMul α)

section

variable [LE α] [LT α] [AddGroupOps α] [IsAddGroup α] [IsOrderedAddCommMonoid α]

def lt_of_add_lt_add_left: ∀a b c: α, a + b < a + c → b < c := by
  intro a b c h
  have := add_lt_add_left (a + b) (a + c) (-a) h
  rwa [←add_assoc, ←add_assoc, neg_add_cancel, zero_add, zero_add] at this

def lt_of_add_lt_add_right: ∀a b c: α, a + c < b + c → a < b := by
  intro a b c h
  have := add_lt_add_right (a + c) (b + c) (-c) h
  rwa [add_assoc, add_assoc, add_neg_cancel, add_zero, add_zero] at this

end
