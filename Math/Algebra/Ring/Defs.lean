import Math.Algebra.Semiring.Defs
import Math.Algebra.AddGroupWithOne.Defs

section PreRing

class IsNonUnitalNonAssocRing (α: Type*) [AddGroupOps α] [Mul α] : Prop extends IsAddCommMagma α, IsAddGroup α, IsLeftDistrib α, IsRightDistrib α, IsMulZeroClass α

class IsNonUnitalRing (α: Type*) [AddGroupOps α] [Mul α] : Prop extends IsAddCommMagma α, IsAddGroup α, IsLeftDistrib α, IsRightDistrib α, IsMulZeroClass α, IsSemigroup α

class IsNonAssocRing (α: Type*) [AddGroupWithOneOps α] [Mul α] : Prop extends IsNonUnitalNonAssocRing α, IsMulOneClass α, IsAddGroupWithOne α

def IsNonUnitalNonAssocRing.inst
  [AddGroupOps α] [Mul α]
  [IsAddCommMagma α] [IsAddGroup α]
  [IsLeftDistrib α] [IsRightDistrib α]
  [IsMulZeroClass α]
  : IsNonUnitalNonAssocRing α where

def IsNonUnitalRing.inst
  [AddGroupOps α] [Mul α]
  [IsAddCommMagma α] [IsAddGroup α]
  [IsLeftDistrib α] [IsRightDistrib α]
  [IsMulZeroClass α] [IsSemigroup α]
  : IsNonUnitalRing α where

def IsNonAssocRing.inst
  [AddGroupWithOneOps α] [Mul α]
  [IsAddCommMagma α] [IsAddGroup α]
  [IsLeftDistrib α] [IsRightDistrib α]
  [IsMulZeroClass α] [IsMulOneClass α]
  [IsAddGroupWithOne α]
  : IsNonAssocRing α := { inferInstanceAs (IsAddGroupWithOne α) with }

instance (priority := 100) [AddGroupWithOneOps α] [Mul α] [IsNonAssocRing α] : IsNonUnitalNonAssocRing α where
instance (priority := 100) [AddGroupOps α] [Mul α] [IsNonUnitalRing α] : IsNonUnitalNonAssocRing α where

end PreRing

class RingOps (α: Type*) extends SemiringOps α, AddGroupWithOneOps α where
instance (priority := 50) [SemiringOps α] [Neg α] [Sub α] [IntCast α] [SMul ℤ α] : RingOps α where
instance (priority := 50) [RingOps α] : SemiringOps α where

class IsRing (α: Type*) [RingOps α] : Prop extends IsSemiring α, IsAddGroupWithOne α  where

def IsRing.inst' [RingOps α]
  [IsAddCommMagma α] [IsAddGroupWithOne α] [IsSemigroup α] [IsMulZeroClass α] [IsMulOneClass α] [IsLeftDistrib α] [IsRightDistrib α] [IsMonoid α]  : IsRing α := {
  inferInstanceAs (IsAddGroupWithOne α), inferInstanceAs (IsMonoid α) with
}
def IsRing.inst [RingOps α] [IsSemiring α] [IsAddGroupWithOne α] : IsRing α := {
  inferInstanceAs (IsAddGroupWithOne α), inferInstanceAs (IsMonoid α) with
}

instance [RingOps α] [IsRing α] : IsRing αᵃᵒᵖ := IsRing.inst
instance [RingOps α] [IsRing α] : IsRing αᵐᵒᵖ := IsRing.inst
instance (priority := 500) [RingOps α] [IsRing α] : IsSemiring α := inferInstance

def zsmul_eq_intCast_mul [RingOps α] [IsRing α] (n: ℤ) (x: α) : n • x = n * x := by
  cases n with
  | ofNat n =>
    erw [zsmul_ofNat n, intCast_ofNat, nsmul_eq_natCast_mul]
  | negSucc n =>
    rw [zsmul_negSucc, intCast_negSucc, nsmul_eq_natCast_mul, ←neg_mul]

def intCast_mul_eq_zsmul [RingOps α] [IsRing α] (x: α) (r: Int) : r * x = r • x := by
  rw [zsmul_eq_intCast_mul]

def mul_intCast_eq_zsmul [RingOps α] [IsRing α] (x: α) (r: Int) : x * r = r • x := by
  rw [zsmul_eq_intCast_mul]
  induction r with
  | ofNat r => erw [intCast_ofNat, mul_natCast_eq_nsmul, nsmul_eq_natCast_mul]
  | negSucc r => rw [intCast_negSucc, mul_neg, neg_mul, mul_natCast_eq_nsmul, nsmul_eq_natCast_mul]

def square_neg [RingOps α] [IsRing α] (x: α) : (-x) ^ 2 = x ^ 2 := by
  rw [npow_two, npow_two, mul_neg, neg_mul, neg_neg]

def square_sub  [RingOps α] [IsRing α] [IsCommMagma α] (a b: α) : (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 := by
  rw [sub_eq_add_neg, sub_eq_add_neg, square_add]
  congr 1
  congr 1
  rw [←mul_neg]
  rw [square_neg]

@[norm_cast]
def intCast_mul [RingOps α] [IsRing α] (a b: ℤ) : a * b = ((a * b: Int): α) := by
  rw [intCast_mul_eq_zsmul, intCast_eq_zsmul_one, ←mul_zsmul, intCast_eq_zsmul_one]

@[simp]
def neg_one_mul [RingOps α] [IsRing α] (a: α) : -1 * a = -a := by
  rw [←intCast_one, intCast_neg, ←zsmul_eq_intCast_mul, neg_one_zsmul]

instance [RingOps α] [IsRing α] : IsNonUnitalNonAssocRing α := IsNonUnitalNonAssocRing.inst
instance [RingOps α] [IsRing α] : IsNonUnitalRing α := IsNonUnitalRing.inst
instance [RingOps α] [IsRing α] : IsNonAssocRing α := IsNonAssocRing.inst

instance instRingInt : IsRing Int where
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
