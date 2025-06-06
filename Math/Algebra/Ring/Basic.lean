import Math.Algebra.Algebra.Defs
import Math.Algebra.Semiring.Char
import Math.Algebra.GroupWithZero.Defs
import Math.Algebra.Ring.Hom

instance [AddGroupWithOneOps R] [IsAddGroupWithOne R] [IsAddCommMagma R] : IsModule ℤ R where
  one_smul := one_zsmul
  mul_smul _ _ _ := mul_zsmul _ _ _
  smul_zero := zsmul_zero
  smul_add _ _ _ := zsmul_add _ _ _
  add_smul := add_zsmul
  zero_smul := zero_zsmul

instance (priority := 500) [RingOps R] [IsRing R] : AlgebraMap ℤ R where
  toFun n := n
  map_zero := intCast_zero
  map_one := intCast_one
  map_add := (intCast_add _ _).symm
  map_mul := (intCast_mul _ _).symm

instance [RingOps R] [IsRing R] : Subsingleton (AlgebraMap ℤ R) where
  allEq := by
    intro a b
    cases a with | mk a =>
    cases b with | mk b =>
    congr; apply Subsingleton.allEq

instance [RingOps R] [IsRing R] : IsAlgebra ℤ R where
  commutes r x := by
    show r * x = x * r
    rw [intCast_mul_eq_zsmul, mul_intCast_eq_zsmul]
  smul_def a b := by
    rw [←intCast_mul_eq_zsmul]
    rfl

def ℤ.ofNatHom : ℕ ↪+* ℤ :=  {
  algebraMap with
  inj' _ _ := Int.ofNat.inj
}

instance : HasChar ℤ 0 := HasChar.of_ring_emb ℤ.ofNatHom

instance [AddGroupOps α] [Mul α] [IsNonUnitalNonAssocRing α] [NoZeroDivisors α] : IsMulCancel₀ α where
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
  rw [neg_mul, mul_neg, neg_neg]
  intro g
  replace g : (a + b) * (a - b) = 0 := by
    rw [add_mul, mul_sub, mul_sub, ←add_sub_assoc _ (b * a),
      sub_eq_add_neg (a * a), add_assoc, h, neg_add_cancel,
      add_zero, g, sub_self]
  rcases of_mul_eq_zero g with g | g
  right; exact neg_eq_of_add_right g
  left; apply eq_of_sub_eq_zero
  assumption
