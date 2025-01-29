import Math.Algebra.Ring
import Math.Data.Nat.Basic

instance : Zero nat := ⟨0⟩
instance : One nat := ⟨1⟩

instance : SMul ℕ nat where
  smul x y := nat.ofNat x * y

instance : NatCast nat := ⟨nat.ofNat⟩

instance : IsSemiring nat where
  add_assoc := nat.add_assoc
  add_comm := nat.add_comm
  zero_add := nat.zero_add
  add_zero := nat.add_zero
  natCast_zero := rfl
  natCast_succ x := by
    show _ = _ + nat.succ 0
    rw [nat.add_succ, nat.add_zero]
    rfl
  ofNat_eq_natCast _ := rfl
  mul_assoc := nat.mul_assoc
  zero_mul := nat.zero_mul
  mul_zero := nat.mul_zero
  one_mul := nat.one_mul
  mul_one := nat.mul_one
  left_distrib _ _ _ := nat.mul_add _ _ _
  right_distrib _ _ _ := nat.add_mul _ _ _
  nsmul_succ a b := by
    show _ * _ = _ * _ + _
    erw [nat.lift_add' a 1, nat.add_mul, nat.one_mul]
  npow_succ a b := by
    rw [nat.npow_succ, nat.mul_comm]

instance : IsCommMagma nat where
  mul_comm := nat.mul_comm
