import Math.Data.Matrix.Basic
import Math.Data.Fintype.Algebra

namespace Matrix

instance [Add α] [Zero α] [Mul α] [Fintype k] :
    HMul (Matrix α n k) (Matrix α k m) (Matrix α n m) where
    hMul a b := .of fun i j => Fintype.sum fun k': k => a i k' * b k' j

@[simp]
def hmul_elem [Add α] [Zero α] [Mul α] [Fintype k]
  (a: Matrix α n k) (b: Matrix α k m) (i: n) (j: m): (a * b) i j = Fintype.sum fun k': k => a i k' * b k' j := rfl

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
        rw [Fintype.sum_mul]
    }
    rw [Fintype.sum_sum]
    conv => {
        rhs; arg 1; intro x
        rw [Fintype.mul_sum]
        arg 1; intro y
        rw [←mul_assoc]
    }
    rw [Fintype.sum_sum, Fintype.sum_of_equiv Prod.equivComm]
    rfl

instance [Fintype n]
  [AddMonoidOps α] [Mul α]
  [IsNonUnitalNonAssocSemiring α] [IsSemigroup α]
  : @Std.Associative (Matrix α n n) (· * ·) := ⟨hmul_assoc⟩

open Classical

def zero_hmul [Add α] [Mul α] [Zero α] [Fintype k] [IsAddZeroClass α] [IsMulZeroClass α]
  (a: Matrix α k m) : (0: Matrix α n k) * a = 0 := by
  ext i j
  simp [Fintype.sum]
  rw [List.sum_eq_zero_of_all_zeros]
  rfl
  intro a ha
  rw [List.mem_map] at ha
  obtain ⟨ _, _, rfl⟩ := ha
  apply zero_mul

def hmul_zero [Add α] [Mul α] [Zero α] [Fintype k] [IsAddZeroClass α] [IsMulZeroClass α]
  (a: Matrix α n k) : a * (0: Matrix α k m) = 0 := by
  ext i j
  simp [Fintype.sum]
  rw [List.sum_eq_zero_of_all_zeros]
  rfl
  intro a ha
  rw [List.mem_map] at ha
  obtain ⟨ _, _, rfl⟩ := ha
  apply mul_zero

def one_hmul [Add α] [Zero α] [One α] [Mul α] [f: Fintype n]
  [IsMulZeroClass α] [IsAddZeroClass α] [IsMulOneClass α]
  (a: Matrix α n m) : (1: Matrix α n n) * a = a := by
  ext i j
  simp
  rw [Fintype.sum]
  have ⟨f₀, f₁, eq⟩ := List.mem_iff_append.mp (Fintype.complete i)
  rw [eq,
    List.map_append,
    List.map_cons,
    List.sum_strip_prefix_zeros,
    List.sum_cons,
    List.sum_eq_zero_of_all_zeros,
    add_zero]
  show (if _  then _ else _) * _ = _
  rw [if_pos rfl, one_mul]
  · intro a ha
    rw [List.mem_map] at ha
    obtain ⟨k, hk, rfl⟩ := ha
    show (if _ then _ else _) * _ = _
    rw [if_neg, zero_mul]
    rintro rfl
    have := List.minCount_of_nodup (α := n) _ Fintype.nodup (n := 2) (x := i) ?_
    contradiction
    rw [eq]
    apply List.MinCount.append (n := 0) (m := 2)
    apply List.MinCount.zero
    apply List.MinCount.head
    apply List.mem_iff_MinCount_one.mp
    assumption
  · intro a ha
    rw [List.mem_map] at ha
    obtain ⟨k, hk, rfl⟩ := ha
    show (if _ then _ else _) * _ = _
    rw [if_neg, zero_mul]
    rintro rfl
    have := List.minCount_of_nodup (α := n) _ Fintype.nodup (n := 2) (x := i) ?_
    contradiction
    rw [eq]
    apply List.MinCount.append (n := 1) (m := 1)
    apply List.mem_iff_MinCount_one.mp
    assumption
    apply List.MinCount.head
    apply List.MinCount.zero

def hmul_one [Add α] [Zero α] [One α] [Mul α] [f: Fintype n]
  [IsMulZeroClass α] [IsAddZeroClass α] [IsMulOneClass α]
  (a: Matrix α m n) : a * (1: Matrix α n n) = a := by
  ext i j
  simp
  rw [Fintype.sum]
  have ⟨f₀, f₁, eq⟩ := List.mem_iff_append.mp (Fintype.complete j)
  rw [eq,
    List.map_append,
    List.map_cons,
    List.sum_strip_prefix_zeros,
    List.sum_cons,
    List.sum_eq_zero_of_all_zeros,
    add_zero]
  show _ * (if _  then _ else _) = _
  rw [if_pos rfl, mul_one]
  · intro a ha
    rw [List.mem_map] at ha
    obtain ⟨k, hk, rfl⟩ := ha
    show _ * (if _ then _ else _) = _
    rw [if_neg, mul_zero]
    rintro rfl
    have := List.minCount_of_nodup (α := n) _ Fintype.nodup (n := 2) (x := k) ?_
    contradiction
    rw [eq]
    apply List.MinCount.append (n := 0) (m := 2)
    apply List.MinCount.zero
    apply List.MinCount.head
    apply List.mem_iff_MinCount_one.mp
    assumption
  · intro a ha
    rw [List.mem_map] at ha
    obtain ⟨k, hk, rfl⟩ := ha
    show _ * (if _ then _ else _) = _
    rw [if_neg, mul_zero]
    rintro rfl
    have := List.minCount_of_nodup (α := n) _ Fintype.nodup (n := 2) (x := k) ?_
    contradiction
    rw [eq]
    apply List.MinCount.append (n := 1) (m := 1)
    apply List.mem_iff_MinCount_one.mp
    assumption
    apply List.MinCount.head
    apply List.MinCount.zero

def hmul_add [Add α] [Zero α] [One α] [Mul α] [Fintype K]
  [IsLeftDistrib α] [IsAddCommMagma α] [IsAddSemigroup α]
  [IsAddZeroClass α]
  (k: Matrix α N K) (a b: Matrix α K M) : k * (a + b) = k * a + k * b := by
  ext i j
  simp
  conv => { lhs; arg 1; intro k; rw [mul_add] }
  rw [Fintype.sum_add]

def add_hmul [Add α] [Zero α] [One α] [Mul α] [Fintype K]
  [IsRightDistrib α] [IsAddCommMagma α] [IsAddSemigroup α]
  [IsAddZeroClass α]
  (a b: Matrix α M K) (k: Matrix α K N) : (a + b) * k = a * k + b * k := by
  ext i j
  simp
  conv => { lhs; arg 1; intro k; rw [add_mul] }
  rw [Fintype.sum_add]

end Matrix
