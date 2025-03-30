import Math.Algebra.AddMonoidWithOne.Defs

section Distrib

class IsLeftDistrib (α: Type*) [Add α] [Mul α]: Prop where
  left_distrib (k a b: α): k * (a + b) = k * a + k * b
class IsRightDistrib (α: Type*) [Add α] [Mul α]: Prop where
  right_distrib (a b k: α): (a + b) * k = a * k + b * k

def mul_add [Add α] [Mul α] [IsLeftDistrib α] (k a b: α): k * (a + b) = k * a + k * b := IsLeftDistrib.left_distrib k a b
def add_mul [Add α] [Mul α] [IsRightDistrib α] (a b k: α): (a + b) * k = a * k + b * k := IsRightDistrib.right_distrib a b k

instance [Add α] [Mul α] [IsLeftDistrib α] : IsLeftDistrib αᵃᵒᵖ where
  left_distrib _ _ _ := mul_add (α := α) _ _ _
instance [Add α] [Mul α] [IsRightDistrib α] : IsRightDistrib αᵃᵒᵖ where
  right_distrib _ _ _ := add_mul (α := α) _ _ _

instance [Add α] [Mul α] [IsLeftDistrib α] : IsRightDistrib αᵐᵒᵖ where
  right_distrib _ _ _ := mul_add (α := α) _ _ _
instance [Add α] [Mul α] [IsRightDistrib α] : IsLeftDistrib αᵐᵒᵖ where
  left_distrib _ _ _ := add_mul (α := α) _ _ _

instance (priority := 100) [Add α] [Mul α] [IsCommMagma α] [IsLeftDistrib α] : IsRightDistrib α where
  right_distrib a b k := by
    iterate 3 rw [mul_comm _ k]
    rw [mul_add]
instance (priority := 100) [Add α] [Mul α] [IsCommMagma α] [IsRightDistrib α] : IsLeftDistrib α where
  left_distrib k a b := by
    iterate 3 rw [mul_comm k]
    rw [add_mul]


end Distrib

section PreSemiring

class IsNonUnitalNonAssocSemiring (α: Type*) [AddMonoidOps α] [Mul α] : Prop extends IsAddCommMagma α, IsAddMonoid α, IsLeftDistrib α, IsRightDistrib α, IsMulZeroClass α

class IsNonUnitalSemiring (α: Type*) [AddMonoidOps α] [Mul α] : Prop extends IsAddCommMagma α, IsAddMonoid α, IsLeftDistrib α, IsRightDistrib α, IsMulZeroClass α, IsSemigroup α

class IsNonAssocSemiring (α: Type*) [AddMonoidWithOneOps α] [Mul α] : Prop extends IsNonUnitalNonAssocSemiring α, IsMulOneClass α, IsAddMonoidWithOne α

def IsNonUnitalNonAssocSemiring.inst
  [AddMonoidOps α] [Mul α]
  [IsAddCommMagma α] [IsAddMonoid α]
  [IsLeftDistrib α] [IsRightDistrib α]
  [IsMulZeroClass α]
  : IsNonUnitalNonAssocSemiring α where

def IsNonAssocSemiring.inst
  [AddMonoidWithOneOps α] [Mul α]
  [IsNonUnitalNonAssocSemiring α]
  [IsMulOneClass α]
  [IsAddMonoidWithOne α]
  : IsNonAssocSemiring α where
  natCast_zero := _root_.natCast_zero
  natCast_succ := _root_.natCast_succ
  ofNat_eq_natCast := IsAddMonoidWithOne.ofNat_eq_natCast

instance (priority := 100) [AddMonoidWithOneOps α] [Mul α] [IsNonAssocSemiring α] : IsNonUnitalNonAssocSemiring α where
instance (priority := 100) [AddMonoidOps α] [Mul α] [IsNonUnitalSemiring α] : IsNonUnitalNonAssocSemiring α where

end PreSemiring

section Semiring

class SemiringOps (α: Type*) extends AddMonoidWithOneOps α, MonoidOps α where
instance [AddMonoidWithOneOps α] [MonoidOps α] : SemiringOps α where

class IsSemiring (α: Type*) [SemiringOps α] : Prop extends
  IsAddCommMagma α, IsAddMonoidWithOne α,
  IsSemigroup α, IsMulZeroClass α, IsMulOneClass α,
  IsLeftDistrib α, IsRightDistrib α, IsMonoid α where

def IsSemiring.inst [SemiringOps α] [IsAddCommMagma α] [IsAddMonoidWithOne α] [IsSemigroup α] [IsMulZeroClass α] [IsMulOneClass α] [IsLeftDistrib α] [IsRightDistrib α] [IsMonoid α] : IsSemiring α where
  npow_zero := _root_.npow_zero
  npow_succ := _root_.npow_succ

instance [SemiringOps α] [IsSemiring α] : IsSemiring αᵃᵒᵖ := IsSemiring.inst
instance [SemiringOps α] [IsSemiring α] : IsSemiring αᵐᵒᵖ := IsSemiring.inst

def natCast_mul_eq_nsmul [SemiringOps α] [IsSemiring α] (x: α) (r: Nat) : r * x = r • x := by
  induction r with
  | zero => rw [natCast_zero, zero_mul, zero_nsmul]
  | succ r ih => rw [natCast_succ, add_mul, one_mul, succ_nsmul, ih]

def mul_natCast_eq_nsmul [SemiringOps α] [IsSemiring α] (x: α) (r: Nat) : x * r = r • x := by
  induction r with
  | zero => rw [natCast_zero, mul_zero, zero_nsmul]
  | succ r ih => rw [natCast_succ, mul_add, mul_one, succ_nsmul, ih]

def natCast_mul [SemiringOps α] [IsSemiring α] (a b: ℕ) : ((a * b: Nat): α) = a * b := by
  rw [natCast_mul_eq_nsmul, natCast_eq_nsmul_one, mul_nsmul, natCast_eq_nsmul_one]

def natCast_npow [SemiringOps α] [IsSemiring α] (a n: ℕ) : ((a ^ n: Nat): α) = a ^ n := by
  induction n with
  | zero => rw [Nat.pow_zero, natCast_one, npow_zero]
  | succ n ih => rw [Nat.pow_succ, natCast_mul, npow_succ, ih]

def add_one_mul [Mul α] [Add α] [One α] [IsMulOneClass α] [IsRightDistrib α] (a b: α) : (a + 1) * b = a * b + b := by rw [add_mul, one_mul]
def mul_add_one [Mul α] [Add α] [One α] [IsMulOneClass α] [IsLeftDistrib α] (a b: α) : a * (b + 1) = a * b + a := by rw [mul_add, mul_one]
def one_add_mul [Mul α] [Add α] [One α] [IsMulOneClass α] [IsRightDistrib α] (a b: α) : (1 + a) * b = b + a * b := by rw [add_mul, one_mul]
def mul_one_add [Mul α] [Add α] [One α] [IsMulOneClass α] [IsLeftDistrib α] (a b: α) : a * (1 + b) = a + a * b := by rw [mul_add, mul_one]

def two_mul [AddMonoidWithOneOps α] [Mul α] [IsAddMonoidWithOne α] [IsRightDistrib α] [IsMulOneClass α] (a: α) : 2 * a = a + a := by
  rw [ofNat_eq_natCast, Nat.zero_add, natCast_succ, natCast_succ,
    natCast_zero, zero_add, add_mul, one_mul]
def mul_two [AddMonoidWithOneOps α] [Mul α] [IsAddMonoidWithOne α] [IsLeftDistrib α] [IsMulOneClass α] (a: α) : a * 2 = a + a := by
  rw [ofNat_eq_natCast, Nat.zero_add, natCast_succ, natCast_succ,
    natCast_zero, zero_add, mul_add, mul_one]

def nsmul_eq_natCast_mul [SemiringOps α] [IsSemiring α] (n: ℕ) (x: α) : n • x = n * x := by
  induction n with
  | zero => rw [zero_nsmul, natCast_zero, zero_mul]
  | succ n ih => rw [succ_nsmul, ih, natCast_succ, add_mul, one_mul]

def square_add  [SemiringOps α] [IsSemiring α] [IsCommMagma α] (a b: α) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  rw [mul_assoc]
  simp [two_mul, npow_two, mul_add, add_mul, add_comm b a]
  ac_rfl

instance (priority := 500) [SemiringOps α] [IsSemiring α] : IsNonAssocSemiring α where
  natCast_zero := natCast_zero
  natCast_succ := natCast_succ
  ofNat_eq_natCast := IsAddMonoidWithOne.ofNat_eq_natCast

instance (priority := 500) [SemiringOps α] [IsSemiring α] : IsNonUnitalNonAssocSemiring α where
instance (priority := 500) [SemiringOps α] [IsSemiring α] : IsNonUnitalSemiring α where

end Semiring

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

instance : IsCommMagma Nat where
  mul_comm := Nat.mul_comm

instance : SMul ℕ ℤ where
  smul a b := a * b

instance instSemiringInt : IsSemiring Int where
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

instance : IsCommMagma Int where
  mul_comm := Int.mul_comm
