import Math.Algebra.Monoid.Hom
import Math.Algebra.Module.Defs

variable [SMul R A] [SMul R B] [SMul R C]

namespace LinearMap

section

variable
  (R: Type*) [SMul R A] [SMul R B]
  [AddMonoidOps A] [AddMonoidOps B] [SemiringOps R]
  [IsAddMonoid A] [IsAddMonoid B] [IsAddCommMagma B] [IsSemiring R]
  [IsDistribMulAction R A] [IsModule R B]

def IsZeroHom.ofIsLinearHom [FunLike F A B] [IsSMulHom F R A B] : IsZeroHom F A B where
  map_zero := by
    intro f
    rw [←smul_zero (0: R), map_smul, zero_smul]

instance : IsZeroHom (A →ₗ[R] B) A B := IsZeroHom.ofIsLinearHom R
instance : IsZeroHom (A ↪ₗ[R] B) A B := IsZeroHom.ofIsLinearHom R
instance : IsZeroHom (A ≃ₗ[R] B) A B := IsZeroHom.ofIsLinearHom R

end

section AddMonoid

variable
  [Add A] [AddMonoidOps B] [MonoidOps R]
  [IsMonoid R] [IsAddMonoid B] [IsDistribMulAction R B]

instance instZero : Zero (A →ₗ[R] B) where
  zero := {
    toFun _ := 0
    map_add {_ _} := by simp
    map_smul {r m} := by simp
  }

instance instAdd [IsAddCommMagma B] : Add (A →ₗ[R] B) where
  add f g := {
    toFun x := f x + g x
    map_add := by
      intro x y
      rw [map_add, map_add]
      rw [add_assoc, add_left_comm (f y), ←add_assoc]
    map_smul := by
      intro r x
      rw [map_smul, map_smul, smul_add]
  }

instance instNSMul [IsAddCommMagma B]: SMul ℕ (A →ₗ[R] B) where
  smul n f := {
    toFun x := n • f x
    map_add := by
      intro x y
      simp [map_add, nsmul_add]
    map_smul := by
      intro r x
      simp [map_smul]
      rw [smul_comm]
  }

instance instSMul [IsCommMagma R]: SMul R (A →ₗ[R] B) where
  smul r f := {
    toFun x := r • f x
    map_add := by
      intro x y
      rw [map_add, smul_add]
    map_smul := by
      intro r x
      rw [map_smul, smul_comm]
  }

@[simp] def apply_zero
  (x: A) : (0: A →ₗ[R] B) x = 0 := rfl
@[simp] def apply_add [IsAddCommMagma B]
  (f g: A →ₗ[R] B) (x: A) : (f + g) x = f x + g x := rfl
@[simp] def apply_nsmul [IsAddCommMagma B]
  (n: ℕ) (f: A →ₗ[R] B) (x: A) : (n • f) x = n • f x := rfl
@[simp] def apply_smul [IsCommMagma R]
  (f: A →ₗ[R] B) (r: R) (x: A) : (r • f) x = r • f x := rfl

instance [IsAddCommMagma B] [IsCommMagma R] : IsAddMonoid (A →ₗ[R] B) where
  add_assoc _ _ _ := by ext; apply add_assoc
  zero_add _ := by ext; apply zero_add
  add_zero _ := by ext; apply add_zero
  zero_nsmul _ := by ext; apply zero_nsmul
  succ_nsmul _ _ := by ext; apply succ_nsmul

instance [IsAddCommMagma B] : IsAddCommMagma (A →ₗ[R] B) where
  add_comm a b := by ext; apply add_comm

instance [IsAddCommMagma B] [IsCommMagma R] : IsDistribMulAction R (A →ₗ[R] B) where
  one_smul _ := by ext; apply one_smul
  mul_smul _ _ _ := by ext; apply mul_smul
  smul_zero _ := by ext; apply smul_zero
  smul_add _ _ _ := by ext; apply smul_add

end AddMonoid

section AddMonoidWithOne

variable
  [AddMonoidOps A] [IsAddMonoid A] [IsAddCommMagma A]
  [MonoidOps R] [IsMonoid R] [IsCommMagma R] [IsDistribMulAction R A]

instance [Add A] : One (A →ₗ[R] A) where
  one := .id _

def apply_one [Add A] (a: A) : (1: A →ₗ[R] A) a = a := rfl

instance : NatCast (A →ₗ[R] A) where
  natCast n := n • 1

instance : IsAddMonoidWithOne (A →ₗ[R] A) where
  natCast_zero := zero_nsmul _
  natCast_succ _ := succ_nsmul _ _

end AddMonoidWithOne

section Module

variable
  [Add A] [AddMonoidOps B] [SemiringOps R]
  [IsSemiring R] [IsAddMonoid B] [IsAddCommMagma B]
  [IsCommMagma R] [IsModule R B]

instance : IsModule R (A →ₗ[R] B) where
  zero_smul f := by ext; apply zero_smul
  add_smul _ _ _ := by ext; apply add_smul

end Module

section AddGroup

variable
  [Add A] [AddGroupOps B] [MonoidOps R]
  [IsMonoid R] [IsAddGroup B] [IsDistribMulAction R B]

instance instNeg [IsAddCommMagma B] : Neg (A →ₗ[R] B) where
  neg f := {
    toFun x := -f x
    map_add {_ _} := by
      simp [map_add, neg_add_rev]
      rw [add_comm]
    map_smul {r m} := by
      rw [neg_smul', map_smul]
  }

instance instSub [IsAddCommMagma B] : Sub (A →ₗ[R] B) where
  sub f g := (f + -g).copy (fun x => f x - g x) <| by
    ext x
    simp
    rw [sub_eq_add_neg]; rfl

instance instNZMul [IsAddCommMagma B]: SMul ℤ (A →ₗ[R] B) where
  smul n f := (match n with
    | .ofNat n => n • f
    | .negSucc n => -((n + 1) • f)).copy (fun x => n • f x) <| by
      ext a
      cases n <;> simp
      rw [zsmul_ofNat]
      rw [zsmul_negSucc]
      rfl

@[simp] def apply_neg [IsAddCommMagma B]
  (f: A →ₗ[R] B) (x: A) : (-f) x = -f x := rfl
@[simp] def apply_sub [IsAddCommMagma B]
  (f g: A →ₗ[R] B) (x: A) : (f - g) x = f x - g x := rfl
@[simp] def apply_zsmul [IsAddCommMagma B]
  (n: ℤ) (f: A →ₗ[R] B) (x: A) : (n • f) x = n • f x := rfl

instance [IsAddCommMagma B] [IsCommMagma R] : IsAddGroup (A →ₗ[R] B) where
  sub_eq_add_neg _ _ := by ext; apply sub_eq_add_neg
  neg_add_cancel _ := by ext; apply neg_add_cancel
  zsmul_ofNat _ _ := by ext; apply zsmul_ofNat
  zsmul_negSucc _ _ := by ext; apply zsmul_negSucc

end AddGroup

section AddGroupWithOne

variable
  [AddGroupOps A] [IsAddGroup A] [IsAddCommMagma A]
  [MonoidOps R] [IsMonoid R] [IsCommMagma R] [IsDistribMulAction R A]

instance : IntCast (A →ₗ[R] A) where
  intCast n := n • 1

instance : IsAddGroupWithOne (A →ₗ[R] A) := {
  inferInstanceAs (IsAddGroup (A →ₗ[R] A)),
  inferInstanceAs (IsAddMonoidWithOne (A →ₗ[R] A)) with
  intCast_ofNat _ := zsmul_ofNat _ _
  intCast_negSucc _ := zsmul_negSucc _ _
}

end AddGroupWithOne

end LinearMap

/-- A shorthand for the type of `R`-bilinear `Nₗ`-valued maps on `M`. -/
abbrev BilinMap
  (R A B: Type*)
  [Add A] [AddMonoidOps B] [MonoidOps R]
  [IsMonoid R] [IsCommMagma R]
  [IsAddMonoid B] [IsAddCommMagma B]
  [SMul R A] [SMul R B] [IsDistribMulAction R B]
  : Type _ := A →ₗ[R] A →ₗ[R] B

def BilinMap.mk
  [Add A] [AddMonoidOps B] [MonoidOps R]
  [IsMonoid R] [IsCommMagma R]
  [IsAddMonoid B] [IsAddCommMagma B]
  [SMul R A] [SMul R B] [IsDistribMulAction R B]
  (f: A -> A -> B)
  (map_add_left: ∀(a b k: A), f (a + b) k = f a k + f b k)
  (map_add_right: ∀(k a b: A), f k (a + b) = f k a + f k b)
  (map_smul_left: ∀(r: R) (a k: A), f (r • a) k = r • f a k)
  (map_smul_right: ∀(r: R) (a k: A), f k (r • a) = r • f k a)
  : A →ₗ[R] A →ₗ[R] B where
  toFun x := {
    toFun y := f x y
    map_add := map_add_right _ _ _
    map_smul := map_smul_right _ _ _
  }
  map_add := by
    intro a b
    ext k
    apply map_add_left
  map_smul := by
    intro a b
    ext k
    apply map_smul_left

@[simp]
def BilinMap.apply_mk
  [Add A] [AddMonoidOps B] [MonoidOps R]
  [IsMonoid R] [IsCommMagma R]
  [IsAddMonoid B] [IsAddCommMagma B]
  [SMul R A] [SMul R B] [IsDistribMulAction R B]
  (f: A -> A -> B)
  {map_add_left: ∀(a b k: A), f (a + b) k = f a k + f b k}
  {map_add_right: ∀(k a b: A), f k (a + b) = f k a + f k b}
  {map_smul_left: ∀(r: R) (a k: A), f (r • a) k = r • f a k}
  {map_smul_right: ∀(r: R) (a k: A), f k (r • a) = r • f k a}
  (a b: A) : BilinMap.mk f map_add_left map_add_right map_smul_left map_smul_right a b = f a b := rfl
