import Math.Type.Notation
import Math.Order.Notation

def OrderDual (α: Type*) := α
abbrev OrderDual.get : OrderDual α -> α := id
abbrev OrderDual.mk : α -> OrderDual α := id

instance [LE α] : LE (OrderDual α) where
  le a b := b.get ≤ a.get
instance [LT α] : LT (OrderDual α) where
  lt a b := b.get < a.get
instance [Inf α] : Sup (OrderDual α) where
  sup a b := .mk (a.get ⊓ b.get)
instance [Sup α] : Inf (OrderDual α) where
  inf a b := .mk (a.get ⊔ b.get)
