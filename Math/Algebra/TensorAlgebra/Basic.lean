import Math.Data.Free.Algebra
import Math.Algebra.RingQuot
import Math.Algebra.LinearMap

section TensorAlgebra

variable (R: Type*) {X: Type*} [Zero R] [One R] [Add R] [Mul R] [Pow R ℕ] [SMul ℕ R] [NatCast R] [∀n, OfNat R (n + 2)]
  [IsCommMagma R] [IsSemiring R]
variable (M : Type*) [Zero M] [Add M] [SMul ℕ M] [SMul R M] [IsAddCommMagma M] [IsAddMonoid M] [IsModule R M]

-- force ι to be linear
inductive TensorAlgebra.Rel : FreeAlgebra R M -> FreeAlgebra R M -> Prop where
| add {x y: M} : Rel (FreeAlgebra.ι R (x + y)) (FreeAlgebra.ι R x + FreeAlgebra.ι R y)
| smul {r: R} {x: M} : Rel (FreeAlgebra.ι R (r • x)) (r • FreeAlgebra.ι R x)

def TensorAlgebra := RingQuot (TensorAlgebra.Rel R M)

end TensorAlgebra

namespace TensorAlgebra

variable {R: Type*} [Zero R] [One R] [Add R] [Mul R] [Pow R ℕ] [SMul ℕ R] [NatCast R] [∀n, OfNat R (n + 2)]
  [IsCommMagma R] [IsSemiring R]
variable [Sub R] [Neg R] [SMul ℤ R] [IntCast R] [IsRing R]
variable {M : Type*} [Zero M] [Add M] [SMul ℕ M] [SMul R M] [IsAddCommMagma M] [IsAddMonoid M] [IsModule R M]

section Instances

instance : Zero (TensorAlgebra R M) := inferInstanceAs (Zero (RingQuot (Rel R M)))
instance : One (TensorAlgebra R M) := inferInstanceAs (One (RingQuot (Rel R M)))
instance : Add (TensorAlgebra R M) := inferInstanceAs (Add (RingQuot (Rel R M)))
instance : Sub (TensorAlgebra R M) := inferInstanceAs (Sub (RingQuot (Rel R M)))
instance : Neg (TensorAlgebra R M) := inferInstanceAs (Neg (RingQuot (Rel R M)))
instance : Mul (TensorAlgebra R M) := inferInstanceAs (Mul (RingQuot (Rel R M)))
instance : SMul ℕ (TensorAlgebra R M) := inferInstanceAs (SMul ℕ (RingQuot (Rel R M)))
instance : SMul ℤ (TensorAlgebra R M) := inferInstanceAs (SMul ℤ (RingQuot (Rel R M)))
instance : SMul R (TensorAlgebra R M) := inferInstanceAs (SMul R (RingQuot (Rel R M)))
instance : Pow (TensorAlgebra R M) ℕ := inferInstanceAs (Pow (RingQuot (Rel R M)) ℕ)
instance : AlgebraMap R (TensorAlgebra R M) := inferInstanceAs (AlgebraMap R (RingQuot (Rel R M)))
instance : RingAlgebraMap R (TensorAlgebra R M) := inferInstanceAs (RingAlgebraMap R (RingQuot (Rel R M)))
instance : NatCast (TensorAlgebra R M) := inferInstanceAs (NatCast (RingQuot (Rel R M)))
instance : IntCast (TensorAlgebra R M) := inferInstanceAs (IntCast (RingQuot (Rel R M)))
instance : OfNat (TensorAlgebra R M) n := inferInstanceAs (OfNat (RingQuot (Rel R M)) n)
instance : IsSemiring (TensorAlgebra R M) := inferInstanceAs (IsSemiring (RingQuot (Rel R M)))
instance : IsRing (TensorAlgebra R M) := inferInstanceAs (IsRing (RingQuot (Rel R M)))
instance : IsAlgebra R (TensorAlgebra R M) := inferInstanceAs (IsAlgebra R (RingQuot (Rel R M)))

end Instances

section ι

variable (R: Type*) [Zero R] [One R] [Add R] [Mul R] [Pow R ℕ] [SMul ℕ R] [NatCast R] [∀n, OfNat R (n + 2)]
  [IsCommMagma R] [IsSemiring R]
variable [Sub R] [Neg R] [SMul ℤ R] [IntCast R] [IsRing R]
variable {M : Type*} [Zero M] [Add M] [SMul ℕ M] [SMul R M] [IsAddCommMagma M] [IsAddMonoid M] [IsModule R M]
variable {A: Type*} {X: Type*} [Zero A] [One A] [Add A] [Mul A] [Pow A ℕ] [SMul ℕ A] [NatCast A] [∀n, OfNat A (n + 2)]
  [IsCommMagma A] [IsSemiring A]
  [SMul R A] [AlgebraMap R A]

def ι : M →ₗ[R] (TensorAlgebra R M) where
  toFun x :=  RingQuot.mkAlgHom (S := R) (Rel (R := R) (M := M)) (FreeAlgebra.ι R x)
  resp_add := by
    intro x y
    rw [←resp_add (RingQuot.mkAlgHom (S := R) (Rel (R := R) (M := M)))]
    apply RingQuot.mkSemiringHom_rel
    apply Rel.add
  resp_smul := by
    intro x y
    rw [←resp_smul (RingQuot.mkAlgHom (S := R) (Rel (R := R) (M := M))) (r := x)]
    apply RingQuot.mkSemiringHom_rel
    apply Rel.smul

def lift [IsSemiring A] [IsAlgebra R A] : (M →ₗ[R] A) ≃ (TensorAlgebra R M →ₐ[R] A) where
  toFun := RingQuot.liftAlgHom R ∘ fun f => ⟨FreeAlgebra.lift R f, by
    intro x y r
    cases r
    simp [FreeAlgebra.lift_ι_apply, resp_add]
    simp [FreeAlgebra.lift_ι_apply, resp_smul]⟩
  invFun f := (toLinearMap f).comp (ι R)
  leftInv f := by
    dsimp; apply DFunLike.ext
    intro x
    show  ((RingQuot.liftAlgHom R) ⟨(FreeAlgebra.lift R) f, _⟩)
      ((RingQuot.mkAlgHom R (Rel R M)) (FreeAlgebra.ι R x)) = f x
    rw [RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply]
  rightInv f := by
    dsimp [toLinearMap, LinearMap.comp]
    apply RingQuot.ringQuot_ext
    apply FreeAlgebra.hom_ext
    ext x
    apply Eq.trans
    apply RingQuot.liftAlgHom_mkAlgHom_apply
    apply FreeAlgebra.lift_ι_apply

variable {R: Type*} [Zero R] [One R] [Add R] [Mul R] [Pow R ℕ] [SMul ℕ R] [NatCast R] [∀n, OfNat R (n + 2)]
  [IsCommMagma R] [IsSemiring R]
variable {M : Type*} [Zero M] [Add M] [SMul ℕ M] [SMul R M] [IsAddCommMagma M] [IsAddMonoid M] [IsModule R M]
  [SMul R A] [AlgebraMap R A]

@[simp]
def ι_comp_lift [IsSemiring A] [IsAlgebra R A] (f : M →ₗ[R] A) :
    (toLinearMap <| lift R f).comp (ι R) = f := by
  exact (lift R).coe_symm f

@[simp]
def lift_ι_apply [IsSemiring A] [IsAlgebra R A] (f : M →ₗ[R] A) (x) :
    lift R f (ι R x) = f x := by
    conv => { rhs; rw [←ι_comp_lift f] }
    rfl

@[induction_eliminator]
def induction {motive: TensorAlgebra R M -> Prop}
  (algebraMap: ∀r: R, motive (algebraMap r))
  (ι: ∀x, motive (ι R x))
  (add: ∀x y, motive x -> motive y -> motive (x + y))
  (mul: ∀x y, motive x -> motive y -> motive (x * y))
  (x: TensorAlgebra R M): motive x := by
  induction x using Quot.ind with | mk x =>
  induction x with
  | grade0 => apply algebraMap
  | grade1 x =>
    have := ι x
    unfold TensorAlgebra.ι RingQuot.mkAlgHom RingQuot.mkSemiringHom at this
    apply this
  | add =>
    erw [←RingQuot.mk, ←RingQuot.mk_add]
    apply add
    assumption
    assumption
  | mul =>
    erw [←RingQuot.mk, ←RingQuot.mk_mul]
    apply mul
    assumption
    assumption

def algebraMapInv : TensorAlgebra R M →ₐ[R] R :=
  lift R {
    toFun _ := 0
    resp_add := by
      intro _ _
      rw [add_zero]
    resp_smul := by
      intro _ _
      rw [smul_zero]
  }

unseal RingQuot.liftAlgHom RingQuot.preLiftAlgHom in
def algebraMap_leftInverse :
    Function.IsLeftInverse algebraMapInv (algebraMap (R := R) (A := TensorAlgebra R M)) := fun _ => rfl

def algebraMap_inj : Function.Injective (algebraMap (R := R) (A := TensorAlgebra R M)) := algebraMap_leftInverse.Injective

attribute [irreducible] ι

end ι

end TensorAlgebra
