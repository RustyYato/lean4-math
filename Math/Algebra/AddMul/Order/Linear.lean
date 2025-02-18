import Math.Algebra.AddMul.Order.Preorder
import Math.Order.Linear

instance [LT α] [LE α] [IsLinearOrder α] : IsLinearOrder (AddOfMul α) :=
  inferInstanceAs (IsLinearOrder α)
instance [LT α] [LE α] [IsLinearOrder α] : IsLinearOrder (MulOfAdd α) :=
  inferInstanceAs (IsLinearOrder α)
