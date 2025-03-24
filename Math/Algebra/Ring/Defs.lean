import Math.Algebra.Semiring.Defs
import Math.Algebra.AddGroupWithOne.Defs

class RingOps (α: Type*) extends SemiringOps α, AddGroupWithOneOps α where
instance [SemiringOps α] [Neg α] [Sub α] [IntCast α] [SMul ℤ α] : RingOps α where

class IsRing (α: Type*) [RingOps α] : Prop extends IsSemiring α, IsAddGroupWithOne α  where

instance [RingOps α] [IsSemiring α] [IsAddGroupWithOne α] : IsRing α where
  intCast_ofNat := intCast_ofNat
  intCast_negSucc := intCast_negSucc
  sub_eq_add_neg := sub_eq_add_neg
  zsmul_ofNat := zsmul_ofNat
  zsmul_negSucc := zsmul_negSucc
  neg_add_cancel := neg_add_cancel

instance [RingOps α] [IsRing α] : IsRing αᵃᵒᵖ := inferInstance
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

@[norm_cast]
def intCast_mul [RingOps α] [IsRing α] (a b: ℤ) : a * b = ((a * b: Int): α) := by
  rw [intCast_mul_eq_zsmul, intCast_eq_zsmul_one, ←mul_zsmul, intCast_eq_zsmul_one]

@[simp]
def neg_one_mul [RingOps α] [IsRing α] (a: α) : -1 * a = -a := by
  rw [←intCast_one, intCast_neg, ←zsmul_eq_intCast_mul, neg_one_zsmul]

class IsNonAssocRing (α: Type*) [AddGroupWithOneOps α] [Mul α] : Prop extends IsNonAssocSemiring α, IsAddGroupWithOne α

class IsNonUnitalNonAssocRing (α: Type*) [AddGroupOps α] [Mul α] : Prop extends IsNonUnitalNonAssocSemiring α, IsAddGroup α

instance
  [AddGroupWithOneOps α] [Mul α]
  [h: IsNonAssocSemiring α]
  [g: IsAddGroupWithOne α]
  : IsNonAssocRing α := {
    h, g with
  }

instance
  [AddGroupOps α] [Mul α]
  [h: IsNonUnitalNonAssocSemiring α]
  [g: IsAddGroup α]
  : IsNonUnitalNonAssocRing α := {
    h, g with
  }

instance [RingOps α] [IsRing α] : IsNonAssocRing α := inferInstance
instance [RingOps α] [IsRing α] : IsNonUnitalNonAssocRing α := inferInstance

instance (priority := 100) [RingOps α] [h: IsNonAssocRing α] [g: IsMonoid α] :
  IsRing α := inferInstance
instance (priority := 100) [RingOps α] [h: IsNonUnitalNonAssocRing α]
  [g: IsAddGroupWithOne α] [IsMulOneClass α] : IsNonAssocRing α := inferInstance
instance (priority := 100) [RingOps α] [h: IsNonUnitalNonAssocRing α]
  [g: IsAddGroupWithOne α] [IsMonoid α] : IsRing α := inferInstance

instance : SMul ℕ ℤ where
  smul a b := a * b

instance instRingInt : IsRing Int where
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

instance : IsCommMagma Int where
  mul_comm := Int.mul_comm

instance : IsSemiring Int := instRingInt.toIsSemiring
