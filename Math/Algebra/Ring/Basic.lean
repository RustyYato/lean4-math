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
  map_zero := intCast_zero
  map_one := intCast_one
  map_add := (intCast_add _ _).symm
  map_mul := (intCast_mul _ _).symm

instance [RingOps R] [IsRing R] : IsAlgebra Int R where
  commutes r x := by
    show r * x = x * r
    rw [intCast_mul_eq_zsmul, mul_intCast_eq_zsmul]
  smul_def a b := by
    rw [←intCast_mul_eq_zsmul]
    rfl

def ofNatHom : ℕ ↪+* ℤ where
  toFun := algebraMap
  map_zero := map_zero _
  map_one := map_one _
  map_add := map_add _
  map_mul := map_mul _
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

def mul_self_eq_mul_self_iff [AddGroupOps R] [Mul R]
  [IsNonUnitalNonAssocRing R] [NoZeroDivisors R] (h: a * b = b * a) :
  a * a = b * b ↔ a = b ∨ a = -b := by
  apply flip Iff.intro
  intro g
  rcases g with rfl | rfl
  rfl
  rw [←neg_mul_left, ←neg_mul_right, neg_neg]
  intro g
  replace g : (a + b) * (a - b) = 0 := by
    rw [add_mul, mul_sub, mul_sub, ←add_sub_assoc _ (b * a),
      sub_eq_add_neg (a * a), add_assoc, h, neg_add_cancel,
      add_zero, g, sub_self]
  rcases of_mul_eq_zero g with g | g
  right; exact neg_eq_of_add_right g
  left; apply eq_of_sub_eq_zero
  assumption
