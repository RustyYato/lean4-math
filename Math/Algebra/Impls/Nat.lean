import Math.Algebra.Order

instance : IsOrderedAddCommMonoid Nat where
  add_le_add_left _ _ := Nat.add_le_add_left
  le_iff_nsmul_le := by
    intro a b n npos
    apply Iff.intro
    apply Nat.mul_le_mul_left
    intro h
    apply Nat.le_of_mul_le_mul_left
    assumption
    assumption
