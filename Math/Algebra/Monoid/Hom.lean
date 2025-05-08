import Math.Algebra.Hom.Defs
import Math.Algebra.Monoid.Defs

def map_nsmul
  [FunLike F α β]
  [AddMonoidOps α] [AddMonoidOps β]
  [IsZeroHom F α β] [IsAddHom F α β]
  [IsAddMonoid α] [IsAddMonoid β]
  (f: F) (n: ℕ) (x: α) : f (n • x) = n • f x := by
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul, map_zero]
  | succ n ih => rw [succ_nsmul, succ_nsmul, map_add, ih]

def map_npow
  [FunLike F α β]
  [MonoidOps α] [MonoidOps β]
  [IsOneHom F α β] [IsMulHom F α β]
  [IsMonoid α] [IsMonoid β]
  (f: F) (n: ℕ) (x: α) : f (x ^ n) = (f x) ^ n :=
  map_nsmul f (α := AddOfMul α) (β := AddOfMul β) n x

def map_nsmul_to_npow
  [FunLike F α β]
  [AddMonoidOps α] [MonoidOps β]
  [IsZeroOneHom F α β] [IsAddMulHom F α β]
  [IsAddMonoid α] [IsMonoid β] (f: F) (n: ℕ) (x: α) : f (n • x) = f x ^ n :=
  map_nsmul f (α := α) (β := AddOfMul β) _ _

def map_npow_to_nsmul
  [FunLike F α β]
  [MonoidOps α] [AddMonoidOps β]
  [IsOneZeroHom F α β] [IsMulAddHom F α β]
  [IsMonoid α] [IsAddMonoid β] (f: F) (n: ℕ) (x: α) : f (x ^ n) = n • f x :=
  map_nsmul f (α := AddOfMul α) (β := β) _ _

def nsmulHom [AddMonoidOps α] [IsAddMonoid α] [IsAddCommMagma α] (n: ℕ) : α →+ α where
  toFun x := n • x
  map_zero := by simp
  map_add := by
    intro x y
    rw [nsmul_add]

def npowHom [MonoidOps α] [IsMonoid α] [IsCommMagma α] (n: ℕ) : α →* α where
  toFun x := x ^ n
  map_one := by simp
  map_mul := by
    intro x y
    rw [mul_npow]

def npowHom₀ [MonoidOps α] [Zero α] [IsMonoid α] [IsCommMagma α] [IsMulZeroClass α] (n: ℕ) (h: 0 < n) : α →*₀ α := {
  npowHom n with
  map_zero := by
    show  0 ^ n = 0
    cases n; contradiction
    rw [zero_npow_succ]
}

instance
  [AddMonoidOps α] [IsAddMonoid α]
  [AddMonoidOps β] [IsAddMonoid β]
  [FunLike F α β] [IsAddHom F α β] [IsZeroHom F α β] : IsSMulHom F ℕ α β where
  map_smul := map_nsmul

section

instance [Zero α] [Add α] [Zero β] [Add β] [IsAddZeroClass β] : Zero (α →+ β) where
  zero := {
    toFun i := 0
    map_zero := by simp [map_zero]
    map_add {a b} := by simp [map_add]
  }

instance [Zero α] [Add α] [AddMonoidOps β] [IsAddMonoid β] [IsAddCommMagma β] : Add (α →+ β) where
  add f g := {
    toFun i := f i + g i
    map_zero := by simp [map_zero]
    map_add {a b} := by simp [map_add]; rw [add_assoc, add_left_comm (f b), ←add_assoc]
  }

instance [Zero α] [Add α] [AddMonoidOps β] [IsAddMonoid β] [IsAddCommMagma β] : SMul ℕ (α →+ β) where
  smul n f := {
    toFun i := n • f i
    map_zero := by simp [map_zero]
    map_add {a b} := by simp [map_add, nsmul_add]
  }

instance [Zero α] [Add α] [AddMonoidOps β] [IsAddMonoid β] [IsAddCommMagma β] : IsAddCommMagma (α →+ β) where
  add_comm _ _ := by ext; apply add_comm

instance [Zero α] [Add α] [AddMonoidOps β] [IsAddMonoid β] [IsAddCommMagma β] : IsAddMonoid (α →+ β) where
  add_assoc _ _ _ := by ext; apply add_assoc
  add_zero _ := by ext; apply add_zero
  zero_add _ := by ext; apply zero_add
  zero_nsmul _ := by ext; apply zero_nsmul
  succ_nsmul _ _ := by ext; apply succ_nsmul

end
