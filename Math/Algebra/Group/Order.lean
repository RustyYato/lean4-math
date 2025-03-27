import Math.Algebra.Monoid.Order.Defs
import Math.Algebra.Group.Defs

instance [LE α] [LT α] [AddGroupOps α] [IsOrderedAddCommMonoid α] [IsAddGroup α] : IsOrderedCancelAddCommMonoid α where
  le_of_add_le_add_left := by
    intro k a b h
    have := add_le_add_left _ _ h (-k)
    rwa [←add_assoc, ←add_assoc, neg_add_cancel, zero_add, zero_add] at this

instance [LE α] [LT α] [GroupOps α] [IsOrderedCommMonoid α] [IsGroup α] : IsOrderedCancelCommMonoid α where
  le_of_mul_le_mul_left := le_of_add_le_add_left (α := AddOfMul α)
