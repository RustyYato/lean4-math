import Math.Order.Linear

instance : IsLinearOrder Int where
  lt_iff_le_and_not_le := Int.lt_iff_le_not_le
  le_antisymm := Int.le_antisymm
  le_trans := Int.le_trans
  lt_or_le := by
    intro a b
    if h:a = b then
      right
      rw [h]
    else
      rcases Int.lt_or_gt_of_ne h with ab | ba
      left; assumption
      right; apply Int.le_of_lt; assumption
instance : IsDecidableLinearOrder Int where
