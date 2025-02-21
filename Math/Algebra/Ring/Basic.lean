import Math.Algebra.Basic
import Math.Algebra.Semiring.Char

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

instance : HasChar Int 0 := by
  apply HasChar.of_natCast_eq_zero
  rfl
  intro m h
  cases h
  apply Nat.dvd_refl
