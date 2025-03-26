import Math.Data.Free.Algebra
import Math.Algebra.RingQuot
import Math.Algebra.LinearMap
import Math.Algebra.Module.Hom
import Math.Algebra.Hom
import Math.Algebra.TrivSqZeroExt

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

section Instances

variable {R M : Type*} [AddMonoidOps M] [SMul R M] [IsAddCommMagma M] [IsAddMonoid M]

instance [SemiringOps R] [IsSemiring R] : SemiringOps (TensorAlgebra R M) := RingQuot.instSemiringOps
instance [RingOps R] [IsRing R] : RingOps (TensorAlgebra R M) := RingQuot.instRingOps
instance [SemiringOps R] [IsSemiring R] [IsModule R M] : SMul R (TensorAlgebra R M) := inferInstanceAs (SMul R (RingQuot (Rel R M)))
instance [SemiringOps R] [IsSemiring R] [IsModule R M] : AlgebraMap R (TensorAlgebra R M) := inferInstanceAs (AlgebraMap R (RingQuot (Rel R M)))
instance [SemiringOps R] [IsSemiring R] : IsSemiring (TensorAlgebra R M) := inferInstanceAs (IsSemiring (RingQuot (Rel R M)))
instance [RingOps R] [IsRing R] : IsRing (TensorAlgebra R M) := inferInstanceAs (IsRing (RingQuot (Rel R M)))
instance [SemiringOps R] [IsSemiring R] [IsModule R M] : IsAlgebra R (TensorAlgebra R M) := inferInstanceAs (IsAlgebra R (RingQuot (Rel R M)))

instance [SemiringOps R] [IsSemiring R] : Add (TensorAlgebra R M) := inferInstance
instance [SemiringOps R] [IsSemiring R] : Mul (TensorAlgebra R M) := inferInstance
instance [RingOps R] [IsRing R] : Sub (TensorAlgebra R M) := inferInstance
instance [RingOps R] [IsRing R] : Neg (TensorAlgebra R M) := inferInstance

end Instances

section ι

variable (R: Type*) [SemiringOps R] [IsCommMagma R] [IsSemiring R]
variable {M : Type*} [AddMonoidOps M] [SMul R M] [IsAddCommMagma M] [IsAddMonoid M] [IsModule R M]
variable {A: Type*} {X: Type*} [SemiringOps A] [IsCommMagma A] [IsSemiring A] [SMul R A] [AlgebraMap R A]

def ι : M →ₗ[R] (TensorAlgebra R M) where
  toFun x :=  RingQuot.mkAlgHom (S := R) (Rel (R := R) (M := M)) (FreeAlgebra.ι R x)
  resp_add' := by
    intro x y
    rw [←resp_add (RingQuot.mkAlgHom (S := R) (Rel (R := R) (M := M)))]
    apply RingQuot.mkRingHom_rel
    apply Rel.add
  resp_smul' := by
    intro x y
    rw [←resp_smul (RingQuot.mkAlgHom (S := R) (Rel (R := R) (M := M))) (r := x)]
    apply RingQuot.mkRingHom_rel
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

variable {R: Type*} [SemiringOps R] [IsCommMagma R] [IsSemiring R]
variable {M : Type*} [AddMonoidOps M] [SMul R M] [IsAddCommMagma M] [IsAddMonoid M] [IsModule R M]
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

@[ext]
def hom_ext [IsAlgebra R A] {f g : TensorAlgebra R M →ₐ[R] A}
  (w : f.toLinearMap.comp (ι R) = g.toLinearMap.comp (ι R)) : f = g :=
  (lift R (A := A)  (M := M)).symm.inj w

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
    unfold TensorAlgebra.ι RingQuot.mkAlgHom RingQuot.mkRingHom at this
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

private def algebraMapInv : TensorAlgebra R M →ₐ[R] R :=
  lift R {
    toFun _ := 0
    resp_add' := by
      intro _ _
      rw [add_zero]
    resp_smul' := by
      intro _ _
      rw [smul_zero]
  }

unseal RingQuot.liftAlgHom RingQuot.preLiftAlgHom in
private def algebraMap_leftInverse :
    Function.IsLeftInverse algebraMapInv (algebraMap (R := R) (A := TensorAlgebra R M)) := fun _ => rfl

def algebraMap_inj : Function.Injective (algebraMap (R := R) (A := TensorAlgebra R M)) := algebraMap_leftInverse.Injective

section

variable [SMul R M] [IsModule R M] [SMul Rᵐᵒᵖ M] [IsModule Rᵐᵒᵖ M] [IsCentralScalar R M]

/-- The canonical map from `TensorAlgebra R M` into `TrivSqZeroExt R M` that sends
`TensorAlgebra.ι` to `TrivSqZeroExt.inr`. -/
private def toTrivSqZeroExt: TensorAlgebra R M →ₐ[R] TrivSqZeroExt R M :=
  lift R (TrivSqZeroExt.inrHom)

@[simp]
private def toTrivSqZeroExt_ι (x : M) : toTrivSqZeroExt (ι R x) = TrivSqZeroExt.inr x := lift_ι_apply _ _

end

private def ιInv : TensorAlgebra R M →ₗ[R] M := by
  let hom := ((RingHom.id R).toMulOpp mul_comm)
  let smul: SMul Rᵐᵒᵖ M := SMul.comp hom
  let _ : @IsModule Rᵐᵒᵖ M _ _ _ _ _ _ := IsModule.compHom ((RingHom.id R).toMulOpp mul_comm)
  haveI : IsCentralScalar R M := ⟨fun r m => rfl⟩
  exact (TrivSqZeroExt.sndHom (R := R) (M := M)).comp toTrivSqZeroExt.toLinearMap

private def ι_leftInverse : Function.IsLeftInverse ιInv (ι R : M → TensorAlgebra R M) := fun x ↦
  let hom := ((RingHom.id R).toMulOpp mul_comm)
  let _: SMul Rᵐᵒᵖ M := SMul.comp hom
  let _ : @IsModule Rᵐᵒᵖ M _ _ _ _ _ _ := IsModule.compHom ((RingHom.id R).toMulOpp mul_comm)
  haveI : IsCentralScalar R M := ⟨fun _ _ => rfl⟩
  of_eq_true (Eq.trans (congrArg (fun x_1 ↦ (TrivSqZeroExt.sndHom) x_1 = x) (toTrivSqZeroExt_ι x)) (eq_self x))

@[simp]
theorem ι_inj (x y : M) : ι R x = ι R y ↔ x = y :=
  ι_leftInverse.Injective.eq_iff

attribute [irreducible] ι

end ι

end TensorAlgebra
