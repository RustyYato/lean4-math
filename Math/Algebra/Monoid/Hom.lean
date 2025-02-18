import Math.Algebra.Hom.Defs
import Math.Algebra.Monoid.Defs

def resp_nsmul
  [FunLike F α β]
  [AddMonoidOps α] [AddMonoidOps β]
  [IsZeroHom F α β] [IsAddHom F α β]
  [IsAddMonoid α] [IsAddMonoid β]
  (f: F) (n: ℕ) (x: α) : f (n • x) = n • f x := by
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul, resp_zero]
  | succ n ih => rw [succ_nsmul, succ_nsmul, resp_add, ih]

def resp_npow
  [FunLike F α β]
  [MonoidOps α] [MonoidOps β]
  [IsOneHom F α β] [IsMulHom F α β]
  [IsMonoid α] [IsMonoid β]
  (f: F) (n: ℕ) (x: α) : f (x ^ n) = (f x) ^ n :=
  resp_nsmul f (α := AddOfMul α) (β := AddOfMul β) n x
