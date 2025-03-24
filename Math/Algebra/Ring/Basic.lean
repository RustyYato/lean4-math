import Math.Algebra.Basic
import Math.Algebra.Semiring.Char
import Math.Algebra.GroupWithZero.Defs

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
  resp_add := (intCast_add _ _).symm
  resp_mul := (intCast_mul _ _).symm

instance [RingOps R] [IsRing R] : IsAlgebra Int R where
  commutes r x := by
    show r * x = x * r
    rw [intCast_mul_eq_zsmul, mul_intCast_eq_zsmul]
  smul_def a b := by
    rw [←intCast_mul_eq_zsmul]
    rfl

def ofNatHom : ℕ ↪+* ℤ where
  toFun := algebraMap
  resp_zero := resp_zero _
  resp_one := resp_one _
  resp_add := resp_add _
  resp_mul := resp_mul _
  inj' _ _ := Int.ofNat.inj

instance : HasChar Int 0 := HasChar.of_ring_emb ofNatHom

instance [AddGroupOps α] [Mul α]
  [IsNonUnitalNonAssocRing α] [NoZeroDivisors α]
  : IsMulCancel₀ α where
  mul_left_cancel₀ := by
    intro a b k hk h
    have : k * a - k * b = 0 := by rw [h, sub_self]
    rw [←mul_sub] at this
    rcases of_mul_eq_zero this with g | g
    contradiction
    apply eq_of_sub_eq_zero
    assumption
  mul_right_cancel₀ := by
    intro a b k hk h
    have : a * k - b * k = 0 := by rw [h, sub_self]
    rw [←sub_mul] at this
    rcases of_mul_eq_zero this with g | g
    apply eq_of_sub_eq_zero
    assumption
    contradiction
