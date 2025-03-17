import Math.Order.Linear
import Math.Order.TopBot

instance [LE α] [LT α] [IsLinearOrder α] : IsLinearOrder (WithTop α) :=
  inferInstance
instance [LE α] [LT α] [IsLinearOrder α] : IsLinearOrder (WithBot α) :=
  inferInstance
