import Math.Algebra.Order
import Math.Order.Linear
import Math.Algebra.Basic

instance : One ℤ := ⟨1⟩

instance : SMul ℕ ℤ where
  smul a b := a * b

instance : IsRing Int where
  add_comm := Int.add_comm
  add_assoc := Int.add_assoc
  zero_add := Int.zero_add
  add_zero := Int.add_zero
  natCast_zero := rfl
  natCast_succ _ := rfl
  ofNat_eq_natCast _ := rfl
  mul_assoc := Int.mul_assoc
  zero_mul := Int.zero_mul
  mul_zero := Int.mul_zero
  one_mul := Int.one_mul
  mul_one := Int.mul_one
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul
  zero_nsmul := Int.zero_mul
  succ_nsmul := by
    intro n a
    show (n + 1) * a = _
    rw [Int.add_mul, Int.one_mul]
    rfl
  sub_eq_add_neg _ _ := Int.sub_eq_add_neg
  zsmul_ofNat _ _ := rfl
  zsmul_negSucc := by
    intro n a
    show _ * _ = -(_ * _)
    rw [Int.negSucc_eq, Int.neg_mul_eq_neg_mul]
    rfl
  neg_add_cancel := Int.add_left_neg
  intCast_ofNat _ := rfl
  intCast_negSucc _ := rfl

instance : IsAddCommMagma Int where
  add_comm := Int.add_comm
instance : IsCommMagma Int where
  mul_comm := Int.mul_comm

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

instance [AddGroupWithOneOps R] [IsAddGroupWithOne R] [IsAddCommMagma R] : IsModule Int R where
  one_smul := one_zsmul
  mul_smul _ _ _ := mul_zsmul _ _ _
  smul_zero := zsmul_zero
  smul_add := zsmul_add
  add_smul := add_zsmul
  zero_smul := zero_zsmul

instance (priority := 500) [RingOps R] [IsRing R] : AlgebraMap Int R where
  toFun n := n
  resp_zero := intCast_zero
  resp_one := intCast_one
  resp_add := intCast_add _ _
  resp_mul := intCast_mul _ _

instance [RingOps R] [IsRing R] : IsAlgebra Int R where
  commutes r x := by
    show r * x = x * r
    rw [intCast_mul_eq_zsmul, mul_intCast_eq_zsmul]
  smul_def a b := by
    rw [←intCast_mul_eq_zsmul]
    rfl

instance : NoZeroDivisors Int where
  of_mul_eq_zero := Int.mul_eq_zero.mp

instance : IsNontrivial Int where
  zero_ne_one := by decide

def Int.char_eq : char Int = 0 := by
  apply char_eq_of_natCast_eq_zero
  rfl
  intro m h
  cases Int.ofNat_eq_zero.mp h
  apply Nat.dvd_refl
