import Math.Algebra.AddMul.Order.Preorder
import Math.Order.Partial

instance [LT α] [LE α] [IsPartialOrder α] : IsPartialOrder (AddOfMul α) :=
  inferInstanceAs (IsPartialOrder α)
instance [LT α] [LE α] [IsPartialOrder α] : IsPartialOrder (MulOfAdd α) :=
  inferInstanceAs (IsPartialOrder α)
