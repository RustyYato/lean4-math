import Math.Algebra.Monoid.Hom
import Math.Algebra.Group.Defs

def resp_neg
  [FunLike F α β]
  [AddGroupOps α] [IsAddGroup α] [AddGroupOps β] [IsSubtractionMonoid β]
  [IsZeroHom F α β] [IsAddHom F α β] (f: F) {x: α} : f (-x) = -f x  := by
  symm; apply neg_eq_of_add_left
  rw [←resp_add, add_neg_cancel, resp_zero]

def resp_inv
  [FunLike F α β]
  [GroupOps α] [IsGroup α] [GroupOps β] [IsDivisionMonoid β]
  [IsOneHom F α β] [IsMulHom F α β] (f: F) {x: α} : f (x⁻¹) = (f x)⁻¹ :=
  resp_neg (α := AddOfMul α) (β := AddOfMul β) f

def resp_zsmul
  [FunLike F α β]
  [AddGroupOps α] [AddGroupOps β]
  [IsZeroHom F α β] [IsAddHom F α β]
  [IsAddGroup α] [IsAddGroup β]
  (f: F) (n: ℤ) (x: α) : f (n • x) = n • f x := by
  induction n with
  | ofNat n => rw [zsmul_ofNat, zsmul_ofNat, resp_nsmul]
  | negSucc n => rw [zsmul_negSucc, zsmul_negSucc, resp_neg, resp_nsmul]

def resp_zpow
  [FunLike F α β]
  [GroupOps α] [GroupOps β]
  [IsOneHom F α β] [IsMulHom F α β]
  [IsGroup α] [IsGroup β]
  (f: F) (n: ℤ) (x: α) : f (x ^ n) = (f x) ^ n :=
  resp_zsmul (α := AddOfMul α) (β := AddOfMul β) f n x

def resp_sub
  [FunLike F α β]
  [AddGroupOps α] [AddGroupOps β]
  [IsZeroHom F α β] [IsAddHom F α β]
  [IsAddGroup α] [IsAddGroup β]
  (f: F) {x y: α} : f (x - y) = f x - f y := by
  rw [sub_eq_add_neg, sub_eq_add_neg, resp_add, resp_neg]

def resp_div
  [FunLike F α β]
  [GroupOps α] [GroupOps β]
  [IsOneHom F α β] [IsMulHom F α β]
  [IsGroup α] [IsGroup β]
  (f: F) {x y: α} : f (x / y) = f x / f y :=
  resp_sub (α := AddOfMul α) (β := AddOfMul β) f
