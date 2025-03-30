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

def nsmulHom [AddMonoidOps α] [IsAddMonoid α] [IsAddCommMagma α] (n: ℕ) : α →+ α where
  toFun x := n • x
  resp_zero := by simp
  resp_add := by
    intro x y
    simp
    rw [nsmul_add]

def npowHom [MonoidOps α] [IsMonoid α] [IsCommMagma α] (n: ℕ) : α →* α where
  toFun x := x ^ n
  resp_one := by simp
  resp_mul := by
    intro x y
    simp
    rw [mul_npow]

def npowHom₀ [MonoidOps α] [Zero α] [IsMonoid α] [IsCommMagma α] [IsMulZeroClass α] (n: ℕ) (h: 0 < n) : α →*₀ α := {
  npowHom n with
  resp_zero := by
    show  0 ^ n = 0
    cases n; contradiction
    rw [zero_npow_succ]
}
