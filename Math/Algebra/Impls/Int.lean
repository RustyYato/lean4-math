import Math.Algebra.Order

instance : IsOrderedAddCommMonoid Int where
  add_le_add_left _ _ := Int.add_le_add_left
  le_iff_nsmul_le := by
    intro a b n npos
    apply Iff.intro
    intro h
    apply Int.mul_le_mul_of_nonneg_left
    assumption
    apply le_of_lt
    apply Int.ofNat_pos.mpr
    assumption
    intro h
    apply Int.le_of_mul_le_mul_left
    assumption
    apply Int.ofNat_pos.mpr
    assumption
