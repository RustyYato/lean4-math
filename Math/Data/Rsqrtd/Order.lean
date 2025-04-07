import Math.Data.Rsqrtd.GroupWithZero
import Math.Algebra.Ring.Order.Defs

instance [FieldOps R] [IsField R] [LT R] [LE R]
  [IsStrictOrderedSemiring R] [IsLinearOrder R] : Fact (Rsqrtd.NoSolution (-1: R)) where
  proof r h := by
    have := square_nonneg r
    rw [h] at this
    rw [neg_le_neg_iff, neg_neg, neg_zero] at this
    exact not_lt_of_le this zero_lt_one
