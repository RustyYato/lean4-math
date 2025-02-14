import Math.Algebra.Semiring.Defs
import Math.Algebra.GroupWithOne.Defs

class RingOps (α: Type*) extends SemiringOps α, AddGroupWithOneOps α where
instance [SemiringOps α] [Neg α] [Sub α] [IntCast α] [SMul ℤ α] : RingOps α where

class IsRing (α: Type*) [RingOps α] extends IsSemiring α, IsAddGroupWithOne α : Prop where

-- a shortcut instance to prevent timeouts
instance (priority := 5000) [RingOps α] [IsRing α] : IsSemiring α where
  npow_zero := npow_zero
  npow_succ := npow_succ

instance [RingOps α] [IsSemiring α] [IsAddGroupWithOne α] : IsRing α where
  intCast_ofNat := intCast_ofNat
  intCast_negSucc := intCast_negSucc
  sub_eq_add_neg := sub_eq_add_neg
  zsmul_ofNat := zsmul_ofNat
  zsmul_negSucc := zsmul_negSucc
  neg_add_cancel := neg_add_cancel

instance [RingOps α] [IsRing α] : IsRing αᵐᵒᵖ := inferInstance

def mul_sub [AddGroupOps α] [IsAddGroup α] [Mul α] [IsLeftDistrib α] [IsMulZeroClass α] (k a b: α): k * (a - b) = k * a - k * b := by
  rw [sub_eq_add_neg, sub_eq_add_neg, mul_add]
  congr 1
  symm
  apply neg_eq_of_add_left
  rw [←mul_add, add_neg_cancel, mul_zero]

def sub_mul [AddGroupOps α] [IsAddGroup α] [Mul α] [IsRightDistrib α] [IsMulZeroClass α] (k a b: α): (a - b) * k = a * k - b * k := by
  rw [sub_eq_add_neg, sub_eq_add_neg, add_mul]
  congr 1
  symm
  apply neg_eq_of_add_left
  rw [←add_mul, add_neg_cancel, zero_mul]

def neg_mul_left [AddGroupOps α] [Mul α] [IsAddGroup α] [IsRightDistrib α] [IsMulZeroClass α] (a b: α) : -(a * b) = -a * b := by
  apply neg_eq_of_add_left
  rw [←add_mul, add_neg_cancel, zero_mul]
def neg_mul_right [AddGroupOps α] [Mul α] [IsAddGroup α] [IsLeftDistrib α] [IsMulZeroClass α] (a b: α) : -(a * b) = a * -b := by
  apply neg_eq_of_add_left
  rw [←mul_add, add_neg_cancel, mul_zero]

def zsmul_eq_intCast_mul [RingOps α] [IsRing α] (n: ℤ) (x: α) : n • x = n * x := by
  cases n with
  | ofNat n =>
    erw [zsmul_ofNat n, intCast_ofNat, nsmul_eq_natCast_mul]
  | negSucc n =>
    rw [zsmul_negSucc, intCast_negSucc, nsmul_eq_natCast_mul, neg_mul_left]

def intCast_mul_eq_zsmul [RingOps α] [IsRing α] (x: α) (r: Int) : r * x = r • x := by
  induction r with
  | ofNat r => erw [intCast_ofNat, zsmul_ofNat, natCast_mul_eq_nsmul]
  | negSucc r => rw [intCast_negSucc, zsmul_negSucc, ←neg_mul_left, natCast_mul_eq_nsmul]

def mul_intCast_eq_zsmul [RingOps α] [IsRing α] (x: α) (r: Int) : x * r = r • x := by
  induction r with
  | ofNat r => erw [intCast_ofNat, zsmul_ofNat, mul_natCast_eq_nsmul]
  | negSucc r => rw [intCast_negSucc, zsmul_negSucc, ←neg_mul_right, mul_natCast_eq_nsmul]

def intCast_mul [RingOps α] [IsRing α] (a b: ℤ) : ((a * b: Int): α) = (a: α) * (b: α) := by
  rw [intCast_mul_eq_zsmul, intCast_eq_zsmul_one, mul_zsmul, intCast_eq_zsmul_one]

def add_sub_assoc [AddGroupOps α] [IsAddGroup α] (a b c: α) : a + b - c = a + (b - c) := by
  rw [sub_eq_add_neg, sub_eq_add_neg, add_assoc]

def sub_add_assoc [AddGroupOps α] [IsAddGroup α] (a b c: α) : a - b + c = a + (-b + c) := by
  rw [sub_eq_add_neg, add_assoc]

def add_eq_iff_eq_sub [AddGroupOps α] [IsAddGroup α]
  (a b c: α) : a + b = c ↔ a = c - b := by
  apply Iff.intro
  intro h
  rw [←h, add_sub_assoc, sub_self, add_zero]
  intro h
  rw [h, sub_add_assoc, neg_add_cancel, add_zero]

def zero_sub [AddGroupOps α] [IsAddGroup α]
  (a: α) : 0 - a = -a := by
  refine neg_eq_of_add_right ?_
  rw [sub_add_assoc, neg_add_cancel, add_zero]

class IsNonAssocRing (α: Type*) [AddGroupWithOneOps α] [Mul α] extends IsNonAssocSemiring α, IsAddGroupWithOne α: Prop

instance
  [AddGroupWithOneOps α] [Mul α]
  [h: IsNonAssocSemiring α]
  [g: IsAddGroupWithOne α]
  : IsNonAssocRing α := {
    h, g with
  }

instance [RingOps α] [IsRing α] : IsNonAssocRing α := inferInstance

instance (priority := 100) [RingOps α] [h: IsNonAssocRing α] [g: IsMonoid α] :
  IsRing α := inferInstance
