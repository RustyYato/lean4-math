-- the endomorphism algebra of linear operations

import Math.Algebra.Module.LinearMap.Defs
import Math.Algebra.Algebra.Defs

namespace LinearMap.End

section Monoid

variable
  [AddMonoidOps A] [IsAddMonoid A] [IsAddCommMagma A]
  [MonoidOps R] [IsMonoid R] [IsCommMagma R]
  [SMul R A] [IsDistribMulAction R A]

scoped instance : Mul (A →ₗ[R] A) where
  mul a b := a.comp b

scoped instance : Pow (A →ₗ[R] A) ℕ := instNPowrec

instance : IsMonoid (A →ₗ[R] A) where
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl

instance : IsLeftDistrib (A →ₗ[R] A) where
  mul_add k a b := by ext; apply map_add k
instance : IsRightDistrib (A →ₗ[R] A) where
  add_mul _ _ _ := rfl

def mul_eq_comp (a b: A →ₗ[R] A) : a * b = a.comp b := rfl

def apply_mul (a b: A →ₗ[R] A) (x: A) : (a * b) x = a (b x) := rfl

end Monoid

section Semiring

variable
  [AddMonoidOps A] [IsAddMonoid A] [IsAddCommMagma A]
  [SemiringOps R] [IsSemiring R] [IsCommMagma R]
  [SMul R A] [IsModule R A]

instance : IsMulZeroClass (A →ₗ[R] A) where
  zero_mul _ := by ext; rfl
  mul_zero a := by ext; apply map_zero a

instance (priority := 2000) : SemiringOps (A →ₗ[R] A) := inferInstance
instance : IsSemiring (A →ₗ[R] A) := IsSemiring.inst

end Semiring

section Ring

variable
  [AddGroupOps A] [IsAddGroup A] [IsAddCommMagma A]
  [RingOps R] [IsRing R] [IsCommMagma R]
  [SMul R A] [IsModule R A]

instance (priority := 2000) : RingOps (A →ₗ[R] A) := inferInstance
instance : IsRing (A →ₗ[R] A) := IsRing.inst

end Ring

section Algebra

variable
  [AddMonoidOps A] [IsAddMonoid A] [IsAddCommMagma A]
  [SemiringOps R] [IsSemiring R] [IsCommMagma R]
  [SMul R A] [IsModule R A]

instance : AlgebraMap R (A →ₗ[R] A) where
  toFun r := r • 1
  map_zero := by rw [zero_smul]
  map_add {x y} := by rw [add_smul]
  map_one := by rw [one_smul]
  map_mul {x y} := by ext a; apply mul_smul

instance : IsAlgebra R (A →ₗ[R] A) where
  smul_def _ _ := rfl
  commutes := by intro r f; ext x; symm; apply map_smul f

def apply_algebraMap (r: R) (x: A) : (algebraMap r: A →ₗ[R] A) x = r • x := rfl

end Algebra

end LinearMap.End
