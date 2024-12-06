import Math.Algebra.Order
import Math.Order.Linear

instance : One ℕ := ⟨1⟩
instance : SMul ℕ ℕ := ⟨(· * ·)⟩

instance : IsSemiring Nat where
  add_comm := Nat.add_comm
  add_assoc := Nat.add_assoc
  zero_add := Nat.zero_add
  add_zero := Nat.add_zero
  natCast_zero := rfl
  natCast_succ _ := rfl
  ofNat_zero := rfl
  ofNat_one := rfl
  ofNat_eq_natCast _ := rfl
  mul_assoc := Nat.mul_assoc
  zero_mul := Nat.zero_mul
  mul_zero := Nat.mul_zero
  one_mul := Nat.one_mul
  mul_one := Nat.mul_one
  left_distrib := Nat.mul_add
  right_distrib := Nat.add_mul
  nsmul_zero := Nat.zero_mul
  nsmul_succ := Nat.succ_mul

instance : IsCommMagma Nat where
  mul_comm := Nat.mul_comm

instance : IsLinearOrder Nat where
  le_antisymm := Nat.le_antisymm
  le_trans := Nat.le_trans
  lt_iff_le_and_not_le := Nat.lt_iff_le_not_le
  lt_or_le := Nat.lt_or_ge

instance : IsOrderedAddCommMonoid Nat where
  add_le_add_left _ _ := Nat.add_le_add_left
