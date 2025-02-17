import Math.Data.Matrix.Basic
import Math.Data.Fintype.Algebra

namespace Matrix

instance [Add α] [Zero α] [Mul α] [Fintype k] :
    HMul (Matrix α n k) (Matrix α k m) (Matrix α n m) where
    hMul a b := .of fun i j => Fintype.sum fun k': k => a i k' * b k' j

def hmul_eq [Add α] [Zero α] [Mul α] [Fintype k]
  (a: Matrix α n k) (b: Matrix α k m): a * b = .of fun i j => Fintype.sum fun k': k => a i k' * b k' j := rfl

-- multiplication is associative for matrices over any non-unital semiring
def hmul_assoc [AddMonoidOps α] [Mul α]
    [IsNonUnitalNonAssocSemiring α] [IsSemigroup α]
    [Fintype n₁] [Fintype n₂]
    (a: Matrix α n₀ n₁) (b: Matrix α n₁ n₂) (c: Matrix α n₂ n₃):
    a * b * c = a * (b * c) := by
    ext i j
    simp [hmul_eq, DFunLike.coe]
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

end Matrix
