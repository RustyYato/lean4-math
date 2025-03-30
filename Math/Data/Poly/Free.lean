import Math.Data.Free.Algebra
import Math.Data.Poly.Eval
import Math.Algebra.RingQuot

-- show that polynomials are precicely the commutative free algebra over a
-- commutative semiring

open Poly

inductive CommFreeAlgebra.Rel (P X: Type*) [SemiringOps P] [IsSemiring P] [IsCommMagma P] :  FreeAlgebra P X -> FreeAlgebra P X -> Prop where
| mul_comm (a b: FreeAlgebra P X) : Rel P X (a * b) (b * a)

def CommFreeAlgebra (P X: Type*) [SemiringOps P] [IsSemiring P] [IsCommMagma P] :=
  RingQuot (CommFreeAlgebra.Rel P X)

variable {P X} [SemiringOps P] [IsSemiring P] [IsCommMagma P]

instance : SemiringOps (CommFreeAlgebra P X) := inferInstanceAs (SemiringOps (RingQuot _))
instance : IsSemiring (CommFreeAlgebra P X) := inferInstanceAs (IsSemiring (RingQuot _))
instance : SMul P (CommFreeAlgebra P X) := inferInstanceAs (SMul _ (RingQuot _))
instance : AlgebraMap P (CommFreeAlgebra P X) := inferInstanceAs (AlgebraMap _ (RingQuot _))
instance : IsAlgebra P (CommFreeAlgebra P X) := inferInstanceAs (IsAlgebra _ (RingQuot _))
instance : IsCommMagma (CommFreeAlgebra P X) where
  mul_comm a b := by
    obtain ⟨a, rfl⟩ := RingQuot.mkRingHom_surj a
    obtain ⟨b, rfl⟩ := RingQuot.mkRingHom_surj b
    rw [←resp_mul (RingQuot.mkRingHom _), ←resp_mul (RingQuot.mkRingHom _)]
    apply RingQuot.mkRingHom_rel
    apply CommFreeAlgebra.Rel.mul_comm

def CommFreeAlgebra.lift (P: Type*)
  [SemiringOps P] [IsSemiring P] [IsCommMagma P] [SemiringOps A] [IsSemiring A] [IsCommMagma A]
  [AlgebraMap P A] [SMul P A] [IsAlgebra P A] : (X -> A) ≃ (CommFreeAlgebra P X →ₐ[P] A) :=
  flip Equiv.trans (RingQuot.liftAlgHom (A := FreeAlgebra P X) (B := A) P) <| {
    toFun f := {
      val := FreeAlgebra.lift P f
      property := by
        intro x y h
        cases h
        rw [resp_mul, resp_mul, mul_comm]
    }
    invFun f x := f.val (FreeAlgebra.ι _ x)
    leftInv := by
      intro f; ext x
      simp
    rightInv := by
      intro ⟨f, hf⟩; ext x
      induction x with
      | grade0 => rw [resp_algebraMap, resp_algebraMap]
      | grade1 => rw [FreeAlgebra.lift_ι_apply]
      | add _ _ => rw [resp_add, resp_add]; congr
      | mul => rw [resp_mul, resp_mul]; congr
  }

def CommFreeAlgebra.ι (P: Type*) [SemiringOps P] [IsSemiring P] [IsCommMagma P] (x: X) : CommFreeAlgebra P X :=
  RingQuot.mkAlgHom P _ (FreeAlgebra.ι P x)

def CommFreeAlgebra.lift_ι_apply
  [SemiringOps A] [IsSemiring A] [IsCommMagma A]
  [AlgebraMap P A] [SMul P A] [IsAlgebra P A]
  (f : X → A) (x) : lift P f (ι P x) = f x := by
  simp [lift, flip]
  erw [RingQuot.liftAlgHom_mkAlgHom_apply]
  apply FreeAlgebra.lift_ι_apply

-- Polynomials are algebraically equivalent to the commutative free algebra
def poly_equiv_free_alg : P[X] ≃ₐ[P] CommFreeAlgebra P Unit where
  toFun := evalHom (CommFreeAlgebra.ι P ())
  invFun a := CommFreeAlgebra.lift P (fun x => Poly.X) a
  leftInv := by
    intro p
    simp
    induction p using Poly.alg_induction with
    | C => rw [evalHom_C, resp_algebraMap]; rfl
    | X => rw [evalHom_X, CommFreeAlgebra.lift_ι_apply]
    | add => rw [resp_add, resp_add]; congr
    | mul => rw [resp_mul, resp_mul]; congr
  rightInv := by
    intro p
    obtain ⟨p, rfl⟩ := RingQuot.mkAlgHom_surj P _ p
    induction p with
    | grade0 r =>
      rw [resp_algebraMap]
      simp
      erw [resp_algebraMap ((CommFreeAlgebra.lift P (fun x => Poly.X))) r]
      rw [←C_eq_algebraMap, evalHom_C]
      rfl
    | grade1 =>
      simp
      erw [RingQuot.liftAlgHom_mkAlgHom_apply,
        FreeAlgebra.lift_ι_apply, evalHom_X]
      rfl
    | add _ _ =>
      simp
      rw [resp_add, resp_add, resp_add]; congr
    | mul =>
      simp
      rw [resp_mul, resp_mul, resp_mul]; congr
  resp_zero := by
    simp; rw [←resp_zero C, evalHom_C, resp_zero]
  resp_one := by
    simp; rw [←resp_one C, evalHom_C, resp_one]
  resp_add {x y} := by
    simp
    rw [resp_add]
  resp_mul {x y} := by
    simp
    rw [resp_mul]
  resp_algebraMap r := by
    simp
    rw [←C_eq_algebraMap, evalHom_C]
