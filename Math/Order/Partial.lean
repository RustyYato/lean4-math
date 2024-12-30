import Math.Order.Preorder

class IsPartialOrder (α: Type*) [LT α] [LE α] extends IsPreOrder α: Prop where
  le_antisymm: ∀{a b: α}, a ≤ b -> b ≤ a -> a = b

variable {α: Type*} {a b c d: α}
variable [LT α] [LE α] [IsPartialOrder α]

def le_antisymm: a ≤ b -> b ≤ a -> a = b := IsPartialOrder.le_antisymm

def lt_or_eq_of_le: a ≤ b -> a < b ∨ a = b := by
  intro h
  by_cases g:b ≤ a
  right
  apply le_antisymm
  assumption
  assumption
  left
  apply lt_iff_le_and_not_le.mpr
  apply And.intro <;> assumption
def lt_of_le_of_ne: a ≤ b -> a ≠ b -> a < b := by
  intro h g
  cases lt_or_eq_of_le h
  assumption
  contradiction

instance [IsPartialOrder α] : IsPartialOrder (OrderDual α) where
  le_antisymm := by
    intro a b ab ba
    apply le_antisymm (α := α) <;> assumption
