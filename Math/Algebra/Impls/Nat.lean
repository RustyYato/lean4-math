import Math.Algebra.Basic
import Math.Algebra.Group.Units
import Math.Algebra.Semiring.Char
import Math.Algebra.Order
import Math.Order.Linear

instance : One ℕ := ⟨1⟩

instance : IsSemiring Nat where
  add_comm := Nat.add_comm
  add_assoc := Nat.add_assoc
  zero_add := Nat.zero_add
  add_zero := Nat.add_zero
  natCast_zero := rfl
  natCast_succ _ := rfl
  ofNat_eq_natCast _ := rfl
  mul_assoc := Nat.mul_assoc
  zero_mul := Nat.zero_mul
  mul_zero := Nat.mul_zero
  one_mul := Nat.one_mul
  mul_one := Nat.mul_one
  left_distrib := Nat.mul_add
  right_distrib := Nat.add_mul
  zero_nsmul := Nat.zero_mul
  succ_nsmul := Nat.succ_mul

instance : IsAddCommMagma Nat where
  add_comm := Nat.add_comm
instance : IsCommMagma Nat where
  mul_comm := Nat.mul_comm

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

instance [AddMonoidWithOneOps R] [IsAddMonoidWithOne R] [IsAddCommMagma R] : IsModule Nat R where
  one_smul := one_nsmul
  mul_smul _ _ _ := mul_nsmul _ _ _
  smul_zero := nsmul_zero
  smul_add := nsmul_add
  add_smul := add_nsmul
  zero_smul := zero_nsmul

instance (priority := 500) [SemiringOps R] [IsSemiring R] : AlgebraMap Nat R where
  toFun n := n
  resp_zero := natCast_zero
  resp_one := natCast_one
  resp_add := natCast_add _ _
  resp_mul := natCast_mul _ _

instance [SemiringOps R] [IsSemiring R] : IsAlgebra Nat R where
  commutes r x := by
    show r * x = x * r
    rw [natCast_mul_eq_nsmul, mul_natCast_eq_nsmul]
  smul_def a b := by
    rw [←natCast_mul_eq_nsmul]
    rfl

instance : NoZeroDivisors Nat where
  of_mul_eq_zero := Nat.mul_eq_zero.mp

def Nat.char_eq : char Nat = 0 := by
  apply char_eq_of_natCast_eq_zero
  rfl
  intro m h
  cases h
  apply Nat.dvd_refl
