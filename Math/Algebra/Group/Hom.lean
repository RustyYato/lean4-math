import Math.Algebra.Monoid.Hom
import Math.Algebra.Group.Defs

def map_neg
  [FunLike F α β]
  [AddGroupOps α] [IsAddGroup α] [AddGroupOps β] [IsSubtractionMonoid β]
  [IsZeroHom F α β] [IsAddHom F α β] (f: F) {x: α} : f (-x) = -f x  := by
  symm; apply neg_eq_of_add_left
  rw [←map_add, add_neg_cancel, map_zero]

def map_inv
  [FunLike F α β]
  [GroupOps α] [IsGroup α] [GroupOps β] [IsDivisionMonoid β]
  [IsOneHom F α β] [IsMulHom F α β] (f: F) {x: α} : f (x⁻¹) = (f x)⁻¹ :=
  map_neg (α := AddOfMul α) (β := AddOfMul β) f

def map_neg_to_inv
  [FunLike F α β]
  [AddGroupOps α] [IsAddGroup α] [GroupOps β] [IsDivisionMonoid β]
  [IsZeroOneHom F α β] [IsAddMulHom F α β] (f: F) {x: α} : f (-x) = (f x)⁻¹ :=
  map_neg (α := α) (β := AddOfMul β) f

def map_inv_to_neg
  [FunLike F α β]
  [GroupOps α] [IsGroup α] [AddGroupOps β] [IsSubtractionMonoid β]
  [IsOneZeroHom F α β] [IsMulAddHom F α β] (f: F) {x: α} : f x⁻¹ = -f x :=
  map_neg (α := AddOfMul α) (β := β) f

def map_zsmul
  [FunLike F α β]
  [AddGroupOps α] [AddGroupOps β]
  [IsZeroHom F α β] [IsAddHom F α β]
  [IsAddGroup α] [IsAddGroup β]
  (f: F) (n: ℤ) (x: α) : f (n • x) = n • f x := by
  induction n with
  | ofNat n => rw [zsmul_ofNat, zsmul_ofNat, map_nsmul]
  | negSucc n => rw [zsmul_negSucc, zsmul_negSucc, map_neg, map_nsmul]

def map_zpow
  [FunLike F α β]
  [GroupOps α] [GroupOps β]
  [IsOneHom F α β] [IsMulHom F α β]
  [IsGroup α] [IsGroup β]
  (f: F) (n: ℤ) (x: α) : f (x ^ n) = (f x) ^ n :=
  map_zsmul (α := AddOfMul α) (β := AddOfMul β) f n x

def map_zsmul_to_zpow
  [FunLike F α β]
  [AddGroupOps α] [GroupOps β]
  [IsZeroOneHom F α β] [IsAddMulHom F α β]
  [IsAddGroup α] [IsGroup β]
  (f: F) (n: ℤ) (x: α) : f (n • x) = f x ^ n :=
  map_zsmul (α := α) (β := AddOfMul β) f n x

def map_zpow_to_zsmul
  [FunLike F α β]
  [GroupOps α] [AddGroupOps β]
  [IsOneZeroHom F α β] [IsMulAddHom F α β]
  [IsGroup α] [IsAddGroup β]
  (f: F) (n: ℤ) (x: α) : f (x ^ n) = n • f x :=
  map_zsmul (α := AddOfMul α) (β := β) f n x

def map_sub
  [FunLike F α β]
  [AddGroupOps α] [AddGroupOps β]
  [IsZeroHom F α β] [IsAddHom F α β]
  [IsAddGroup α] [IsAddGroup β]
  (f: F) (x y: α) : f (x - y) = f x - f y := by
  rw [sub_eq_add_neg, sub_eq_add_neg, map_add, map_neg]

def map_div
  [FunLike F α β]
  [GroupOps α] [GroupOps β]
  [IsOneHom F α β] [IsMulHom F α β]
  [IsGroup α] [IsGroup β]
  (f: F) (x y: α) : f (x / y) = f x / f y :=
  map_sub (α := AddOfMul α) (β := AddOfMul β) f _ _

def map_sub_to_div
  [FunLike F α β]
  [AddGroupOps α] [GroupOps β]
  [IsZeroOneHom F α β] [IsAddMulHom F α β]
  [IsAddGroup α] [IsGroup β]
  (f: F) (x y: α) : f (x - y) = f x / f y :=
  map_sub (α := α) (β := AddOfMul β) f x y

def map_div_to_sub
  [FunLike F α β]
  [GroupOps α] [AddGroupOps β]
  [IsOneZeroHom F α β] [IsMulAddHom F α β]
  [IsGroup α] [IsAddGroup β]
  (f: F) (x y: α) : f (x / y) = f x - f y  :=
  map_sub (α := AddOfMul α) (β := β) f x y

section

variable [Mul α] [One α] [IsMulOneClass α] [GroupOps β] [IsGroup β]
  [Add α] [Zero α] [IsAddZeroClass α] [AddGroupOps β] [IsAddGroup β]

-- every homomorphism to a group that preserves products also preserves the unit
instance (priority := 500) instOneHomOfMulHom [FunLike F α β] [IsMulHom F α β] : IsOneHom F α β where
  map_one f := by
    rw [←inv_mul_cancel (f 1)]
    apply mul_left_cancel (k := f 1)
    rw [←map_mul, ←mul_assoc, mul_inv_cancel, one_mul, one_mul]

-- every homomorphism to a group that preserves products also preserves the unit
instance (priority := 500) instZeroHomOfAddHom [FunLike F α β] [IsAddHom F α β] : IsZeroHom F α β where
  map_zero := instOneHomOfMulHom.map_one (α := MulOfAdd α) (β := MulOfAdd β)

def GroupHom.ofMulHom (f: MulHom α β) : α →* β := {
    f with
    map_one := map_one f
}

def GroupHom.apply_ofMulHom (f: MulHom α β) (x: α) : GroupHom.ofMulHom f x = f x := rfl

def AddGroupHom.ofAddHom (f: AddHom α β) : α →+ β := {
    f with
    map_zero := map_zero f
}

def AddGroupHom.apply_ofAddHom (f: AddHom α β) (x: α) : AddGroupHom.ofAddHom f x = f x := rfl

end

instance
  {F α β}
  [AddGroupOps α] [IsAddGroup α]
  [AddGroupOps β] [IsAddGroup β]
  [FunLike F α β] [IsAddHom F α β] : IsSMulHom F ℤ α β where
  map_smul := map_zsmul
