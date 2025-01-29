import Math.Algebra.RingHom

section

class AlgebraMap (R A: Type*) [SemiringOps R] [SemiringOps A] extends R →+ₙ* A where

class RingAlgebraMap (R A: Type*) [RingOps R] [RingOps A] extends AlgebraMap R A , R →+* A where

def algebraMap {R A: Type*} [SemiringOps R] [SemiringOps A] [f: AlgebraMap R A]
  : R →+ₙ* A := f.toSemiringHom

def algebraMapᵣ {R A: Type*} [RingOps R] [RingOps A] [f: RingAlgebraMap R A]
  : R →+* A := f.toRingHom

class IsAlgebra (R A: Type*) [SemiringOps R] [SemiringOps A] [SMul R A] [AlgebraMap R A] [IsSemiring A] extends IsSemiring R: Prop where
  commutes: ∀(r: R) (x: A), algebraMap r * x = x * algebraMap r
  smul_def: ∀(r: R) (x: A), r • x = algebraMap r * x

export IsAlgebra (commutes smul_def)

class Algebra (R A: Type*) [SemiringOps A] [IsSemiring A] extends SemiringOps R, IsSemiring R, SMul R A, AlgebraMap R A where
  commutes: ∀(r: R) (x: A), algebraMap r * x = x * algebraMap r
  smul_def: ∀(r: R) (x: A), r • x = algebraMap r * x

instance [SemiringOps A] [IsSemiring A] [a: Algebra R A] : IsAlgebra R A where
  commutes := a.commutes
  smul_def := a.smul_def

end

section Algebra

variable {R A: Type*} [SemiringOps R] [SemiringOps A]

variable [IsCommMagma R] [IsSemiring R] [IsSemiring A] [SMul R A]

abbrev Algebra.ofModule [IsModule R A]
  (h₁ : ∀ (r : R) (x y : A), r • x * y = r • (x * y))
  (h₂ : ∀ (r : R) (x y : A), x * r • y = r • (x * y)) : Algebra R A where
  toFun r := r • (1: A)
  resp_zero := zero_smul _
  resp_one := one_smul _
  resp_add := add_smul _ _ _
  resp_mul := by
    dsimp
    intro x y
    rw [h₁, one_mul, mul_smul]
  commutes := by
    intro r x
    show (r • (1: A)) * x = x * (r • (1: A))
    rw [h₁, one_mul, h₂, mul_one]
  smul_def := by
    intro r x
    show r • x = (r • (1: A)) * x
    rw [h₁, one_mul]

def AlgebraMap.toAlgebra [AlgebraMap R A] (h : ∀(c: R) (x: A), algebraMap c * x = x * algebraMap c) : Algebra R A where
  smul c x := algebraMap c * x
  commutes := by
    intro r x
    rw [h]
  smul_def _ _ := rfl

instance [AlgebraMap R A] [IsAlgebra R A] : IsModule R A where
  one_smul x := by rw [smul_def, resp_one, one_mul]
  zero_smul x := by rw [smul_def, resp_zero, zero_mul]
  mul_smul a b x := by simp [smul_def, resp_mul, mul_assoc]
  smul_zero x := by rw [smul_def, mul_zero]
  smul_add a x y := by rw [smul_def, mul_add, ←smul_def, ←smul_def]
  add_smul a b x := by rw [smul_def, resp_add, add_mul, ←smul_def, ←smul_def]

instance : AlgebraMap R R where
  toFun := id
  resp_one := rfl
  resp_zero := rfl
  resp_add := rfl
  resp_mul := rfl

instance : IsAlgebra R R where
  commutes := mul_comm
  smul_def _ _ := rfl

variable [SemiringOps S] [SMul S A]

instance [AlgebraMap R A] [IsAlgebra R A] [AlgebraMap S A] [IsAlgebra S A] : IsSMulComm R S A where
  smul_comm := by
    intro r s x
    simp [smul_def, ←mul_assoc]
    congr 1
    apply commutes

end Algebra
