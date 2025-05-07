import Math.Algebra.Hom.Defs
import Math.Algebra.Semiring.Defs
import Math.Algebra.Module.Defs

section

def AlgebraMap.ofHom {R A: Type*} [SemiringOps R] [SemiringOps A] (f: R →+* A) : AlgebraMap R A := { f with }

class IsAlgebra (R A: Type*) [SemiringOps R] [SemiringOps A] [SMul R A] [AlgebraMap R A] [IsSemiring A] [IsSemiring R] : Prop where
  commutes: ∀(r: R) (x: A), algebraMap r * x = x * algebraMap r
  smul_def: ∀(r: R) (x: A), r • x = algebraMap r * x

export IsAlgebra (commutes smul_def)

class Algebra (R A: Type*) [SemiringOps A] [IsSemiring A] extends SemiringOps R, IsSemiring R, SMul R A, AlgebraMap R A where
  commutes: ∀(r: R) (x: A), algebraMap r * x = x * algebraMap r
  smul_def: ∀(r: R) (x: A), r • x = algebraMap r * x

instance [SemiringOps A] [IsSemiring A] [a: Algebra R A] : IsAlgebra R A where
  commutes := a.commutes
  smul_def := a.smul_def

variable [SemiringOps R] [SemiringOps A] [SMul R A] [AlgebraMap R A] [IsSemiring A]
  [IsSemiring R] [IsAlgebra R A]

def smul_mul
  (r s: R) (a b: A) : r • a * s • b = (r * s) • (a * b) := by
  simp [smul_def, map_mul]
  rw [mul_assoc, mul_assoc]; congr 1
  rw [←mul_assoc, ←mul_assoc, commutes]

end

section Algebra

variable {R A: Type*} [SemiringOps R] [SemiringOps A]

variable [IsCommMagma R] [IsSemiring R] [IsSemiring A] [SMul R A]

-- a shortcut instance
local instance : IsSemigroup A := inferInstance

abbrev Algebra.ofModule [IsModule R A]
  (h₁ : ∀ (r : R) (x y : A), r • x * y = r • (x * y))
  (h₂ : ∀ (r : R) (x y : A), x * r • y = r • (x * y)) : Algebra R A where
  toFun r := r • (1: A)
  map_zero := zero_smul _
  map_one := one_smul _
  map_add := add_smul _ _ _
  map_mul := by
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
  one_smul x := by rw [smul_def, map_one, one_mul]
  zero_smul x := by rw [smul_def, map_zero, zero_mul]
  mul_smul a b x := by simp [smul_def, map_mul, mul_assoc]
  smul_zero x := by rw [smul_def, mul_zero]
  smul_add a x y := by rw [smul_def, mul_add, ←smul_def, ←smul_def]
  add_smul a b x := by rw [smul_def, map_add, add_mul, ←smul_def, ←smul_def]

instance (priority := 900) : AlgebraMap R R where
  toFun := id
  map_one := rfl
  map_zero := rfl
  map_add := rfl
  map_mul := rfl

def algebraMap_id : algebraMap (R := R) (α := R) x = x := rfl

instance : IsAlgebra R R where
  commutes _ _ := mul_comm _ _
  smul_def _ _ := rfl

variable [SemiringOps S] [SMul S A]

instance [AlgebraMap R A] [IsAlgebra R A] [AlgebraMap S A] [IsSemiring S] [IsAlgebra S A] : IsSMulComm R S A where
  smul_comm r s x := by simp only [smul_def, ←mul_assoc]; rw [commutes]

def smul_one [AlgebraMap S A] [IsSemiring S] [IsAlgebra S A] (s: S) : s • (1: A) = algebraMap s := by
  rw [smul_def, mul_one]

end Algebra

instance (priority := 500) [SemiringOps R] [IsSemiring R] : AlgebraMap Nat R where
  toFun n := n
  map_zero := natCast_zero
  map_one := natCast_one
  map_add := natCast_add _ _
  map_mul := natCast_mul _ _

instance [SemiringOps R] [IsSemiring R] : IsAlgebra Nat R where
  commutes r x := by
    show r * x = x * r
    rw [natCast_mul_eq_nsmul, mul_natCast_eq_nsmul]
  smul_def a b := by
    rw [←natCast_mul_eq_nsmul]
    rfl

section

variable [SemiringOps R] [IsSemiring R] [SemiringOps A] [IsSemiring A] [AlgebraMap R A] [SMul R A] [IsAlgebra R A]

instance (r: R) (a: A) : IsCommutes (algebraMap r) a where
  mul_commutes := commutes _ _
instance (r: R) (a: A) : IsCommutes a (algebraMap r) := inferInstance

instance (priority := 500) : AlgebraMap Rᵐᵒᵖ A where
  toFun r := algebraMap r.get
  map_zero := map_zero algebraMap
  map_add := map_add algebraMap
  map_one := map_one algebraMap
  map_mul := by
    intro x y
    simp
    rw [map_mul, commutes]

instance (priority := 500) : SMul Rᵐᵒᵖ A where
  smul r a := r.get • a

instance (priority := 500) : IsAlgebra Rᵐᵒᵖ A where
  commutes := commutes (R := R)
  smul_def := smul_def (R := R)

instance : IsScalarTower R Rᵐᵒᵖ A where
  smul_assoc := by
    intro x y z
    show (y * .mk x) • z = _
    simp only [smul_def]
    rw [map_mul, mul_assoc]
    rw [mul_left_comm]
    rfl

instance : IsScalarTower Rᵐᵒᵖ R A where
  smul_assoc := by
    intro x y z
    show (y * x.get) • z = _
    simp only [smul_def]
    rw [map_mul, commutes, mul_assoc]
    rfl

instance : IsScalarTower R A A where
  smul_assoc r a b := by
    simp only [smul_def, smul_eq_mul]
    rw [mul_assoc]

instance : IsCentralScalar R A where
  rsmul_eq_lsmul _ _ := rfl

instance : IsCentralScalar Rᵐᵒᵖ A where
  rsmul_eq_lsmul _ _ := rfl

end

section

variable (A B C: Type*) [SemiringOps A] [IsSemiring A] [SemiringOps B] [IsSemiring B]
   [SemiringOps C] [IsSemiring C]
   [AlgebraMap A B] [AlgebraMap B C] [AlgebraMap A C]
   [SMul A B] [SMul B C] [SMul A C]
   [IsAlgebra A B] [IsAlgebra B C] [IsAlgebra A C]

class IsAlgebraTower where
  algebraMap_algebraMap (a: A) : algebraMap (algebraMap a: B) = (algebraMap a: C)

def algebraMap_algebraMap [IsAlgebraTower A B C] (a: A) : algebraMap (algebraMap a: B) = (algebraMap a: C) :=
  IsAlgebraTower.algebraMap_algebraMap a

instance (priority := 900) instScalarTowerOfAlgebraTower [IsAlgebraTower A B C]: IsScalarTower A B C where
  smul_assoc := by
    intro x y z
    simp only [smul_def]
    rw [map_mul]
    rw [mul_assoc, algebraMap_algebraMap]

instance : IsAlgebraTower A B B where
  algebraMap_algebraMap _ := rfl

instance : IsAlgebraTower A A B where
  algebraMap_algebraMap _ := rfl

end
