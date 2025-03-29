import Math.Data.Matrix.Basic
import Math.Data.Fintype.Algebra

namespace Matrix

instance [Add α] [Zero α] [Mul α] [IsAddSemigroup α] [IsAddCommMagma α] [Fintype k] :
    HMul (Matrix α n k) (Matrix α k m) (Matrix α n m) where
    hMul a b := .of fun i j => ∑k': k, a i k' * b k' j

@[simp]
def hmul_elem [Add α] [Zero α] [Mul α] [Fintype k] [IsAddSemigroup α] [IsAddCommMagma α]
  (a: Matrix α n k) (b: Matrix α k m) (i: n) (j: m): (a * b) i j = ∑k': k, a i k' * b k' j := rfl

-- multiplication is associative for matrices over any non-unital semiring
def hmul_assoc [AddMonoidOps α] [Mul α]
    [IsNonUnitalNonAssocSemiring α] [IsSemigroup α]
    [Fintype n₁] [Fintype n₂]
    (a: Matrix α n₀ n₁) (b: Matrix α n₁ n₂) (c: Matrix α n₂ n₃):
    a * b * c = a * (b * c) := by
    ext i j
    simp
    conv => {
        lhs; arg 1; intro x
        rw [sum_mul]
    }
    rw [sum_sum]
    conv => {
        rhs; arg 1; intro x
        rw [mul_sum]
        arg 1; intro y
        rw [←mul_assoc]
    }
    rw [sum_sum]
    apply sum_eq_of_equiv (h := Equiv.commProd _ _)
    intro i; rfl

instance [Fintype n]
  [AddMonoidOps α] [Mul α]
  [IsNonUnitalNonAssocSemiring α] [IsSemigroup α]
  : @Std.Associative (Matrix α n n) (· * ·) := ⟨hmul_assoc⟩

section

def zero_hmul [AddMonoidOps α] [IsAddMonoid α] [Mul α]
    [IsAddCommMagma α] [IsMulZeroClass α] [Fintype k]
  (a: Matrix α k m) : (0: Matrix α n k) * a = 0 := by
  ext i j
  apply sum_eq_zero
  intro i
  apply zero_mul

def hmul_zero [AddMonoidOps α] [IsAddMonoid α] [Mul α]
    [IsAddCommMagma α] [IsMulZeroClass α] [Fintype k]
  (a: Matrix α n k) : a * (0: Matrix α k m) = 0 := by
  ext i j
  apply sum_eq_zero
  intro i
  apply mul_zero

def one_hmul [AddMonoidOps α] [IsAddMonoid α]
    [Mul α] [One α] [IsMulOneClass α] [IsAddCommMagma α]
    [IsMulZeroClass α] [Fintype n] [DecidableEq n]
  (a: Matrix α n m) : (1: Matrix α n n) * a = a := by
  ext i j
  simp
  conv => {
    lhs; arg 1; intro k
    rw [show (if i = k then 1 else 0) * a k j = (if i = k then a k j else 0) by
        split; rw [one_mul]; rw [zero_mul]]
  }
  rw [sum_select_unique]
  intro j
  apply Eq.comm

def hmul_one [AddMonoidOps α] [IsAddMonoid α]
    [Mul α] [One α] [IsMulOneClass α] [IsAddCommMagma α]
    [IsMulZeroClass α] [Fintype n] [DecidableEq n]
  (a: Matrix α m n) : a * (1: Matrix α n n) = a := by
  ext i j
  simp
  conv => {
    lhs; arg 1; intro k
    rw [show a i k * (if k = j then 1 else 0) = (if k = j then a i k else 0) by
        split; rw [mul_one]; rw [mul_zero]]
  }
  rw [sum_select_unique]
  intro j
  rfl

def hmul_add [AddMonoidOps α] [IsAddMonoid α]
    [Mul α] [IsAddCommMagma α]
    [IsLeftDistrib α] [Fintype K]
  (k: Matrix α N K) (a b: Matrix α K M) : k * (a + b) = k * a + k * b := by
  ext i j
  simp
  conv => { lhs; arg 1; intro k; rw [mul_add] }
  rw [sum_add_sum]

def add_hmul [AddMonoidOps α] [IsAddMonoid α]
    [Mul α] [IsAddCommMagma α]
    [IsRightDistrib α] [Fintype K]
  (a b: Matrix α M K) (k: Matrix α K N) : (a + b) * k = a * k + b * k := by
  ext i j
  simp
  conv => { lhs; arg 1; intro k; rw [add_mul] }
  rw [sum_add_sum]

end

instance [Add α] [Zero α] [Mul α] [IsAddSemigroup α] [IsAddCommMagma α] [Fintype n] : Mul (Matrix α n n) where
    mul := HMul.hMul

instance [Add α] [Zero α] [Mul α] [One α] [IsAddSemigroup α] [IsAddCommMagma α] [Fintype n] [DecidableEq n] : Pow (Matrix α n n) ℕ :=
  instNPowrec

instance [RingOps α] [IsNonUnitalNonAssocRing α] [DecidableEq n] [Fintype n] : RingOps (Matrix α n n) := RingOps.mk
instance [Add α] [Zero α] [IsAddSemigroup α] [IsAddCommMagma α] [MonoidOps α] [IsMonoid α] [DecidableEq n] [Fintype n] [DecidableEq n] : MonoidOps (Matrix α n n) := inferInstance

instance
  [AddMonoidOps α] [Mul α]
  [IsNonUnitalNonAssocSemiring α] [DecidableEq n]
  [Fintype n] : IsNonUnitalNonAssocSemiring (Matrix α n n) where
  left_distrib _ _ _ := hmul_add _ _ _
  right_distrib _ _ _ := add_hmul _ _ _
  zero_mul := zero_hmul
  mul_zero := hmul_zero

instance
  [AddMonoidOps α] [Mul α] [IsNonUnitalNonAssocSemiring α] [IsSemigroup α]
  [Fintype n] : IsSemigroup (Matrix α n n) where
  mul_assoc := hmul_assoc

instance
  [AddMonoidWithOneOps α] [Mul α]
  [IsNonAssocSemiring α] [DecidableEq n]
  [Fintype n] : IsMulOneClass (Matrix α n n) where
  one_mul := one_hmul
  mul_one := hmul_one

instance instSemiring [SemiringOps α] [IsSemiring α] [Fintype n] [DecidableEq n] : IsSemiring (Matrix α n n) := {}
instance [RingOps α] [IsRing α] [Fintype n] [DecidableEq n] : IsRing (Matrix α n n) := {
  instSemiring, instAddGroupWithOne with
}

end Matrix
