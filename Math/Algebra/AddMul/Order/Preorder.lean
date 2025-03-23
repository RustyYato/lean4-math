import Math.Algebra.AddMul
import Math.Order.Defs

variable [LE α] [LT α]

instance : LT (AddOfMul α) where
  lt a b := a.get < b.get
instance : LE (AddOfMul α) where
  le a b := a.get ≤ b.get

instance : LT (MulOfAdd α) where
  lt a b := a.get < b.get
instance : LE (MulOfAdd α) where
  le a b := a.get ≤ b.get

instance [IsLawfulLT α] : IsLawfulLT (AddOfMul α) :=
  inferInstanceAs (IsLawfulLT α)

instance [IsPreOrder α] : IsPreOrder (AddOfMul α) :=
  inferInstanceAs (IsPreOrder α)

instance [IsLawfulLT α] : IsLawfulLT (MulOfAdd α) :=
  inferInstanceAs (IsLawfulLT α)

instance [IsPreOrder α] : IsPreOrder (MulOfAdd α) :=
  inferInstanceAs (IsPreOrder α)
