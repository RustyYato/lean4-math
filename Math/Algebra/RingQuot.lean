import Math.Algebra.Ring.Con
import Math.Algebra.Algebra.Con
import Math.Algebra.Algebra.Hom

def RingQuot.Con [Add α] [Mul α] (r: α -> α -> Prop) : RingCon α := RingCon.generate r

def RingQuot [Add α] [Mul α] (r: α -> α -> Prop) : Type _ := AlgQuotient (RingQuot.Con r)

namespace RingQuot

section

variable {r: α -> α -> Prop}

instance instSemiringOps [SemiringOps α] [IsSemiring α] : SemiringOps (RingQuot r) :=
  inferInstanceAs (SemiringOps (AlgQuotient (RingQuot.Con r)))
instance instIsSemiring [SemiringOps α] [IsSemiring α] : IsSemiring (RingQuot r) :=
  inferInstanceAs (IsSemiring (AlgQuotient (RingQuot.Con r)))

instance instRingOps [RingOps α] [IsRing α] : RingOps (RingQuot r) :=
  inferInstanceAs (RingOps (AlgQuotient (RingQuot.Con r)))
instance instIsRing [RingOps α] [IsRing α] : IsRing (RingQuot r) :=
  inferInstanceAs (IsRing (AlgQuotient (RingQuot.Con r)))

variable [SemiringOps α] [SemiringOps S]
  [IsSemiring α] [IsSemiring S]
  [SMul S α] [AlgebraMap S α] [IsAlgebra S α]

instance : SMul S (RingQuot r) :=
  inferInstanceAs (SMul S (AlgQuotient (RingQuot.Con r)))
instance : AlgebraMap S (RingQuot r) :=
  inferInstanceAs (AlgebraMap S (AlgQuotient (RingQuot.Con r)))
instance : IsAlgebra S (RingQuot r) :=
  inferInstanceAs (IsAlgebra S (AlgQuotient (RingQuot.Con r)))

end

variable {r: R -> R -> Prop}

def mk [SemiringOps R] [IsSemiring R] (r: R -> R -> Prop) : R →+* RingQuot r :=
  RingCon.mkQuot _

@[induction_eliminator]
def ind [SemiringOps R] [IsSemiring R] {motive: RingQuot r -> Prop} (mk: ∀x, motive (mk r x)) : ∀q, motive q := by
  intro q
  induction q using AlgQuotient.ind with
  | mk a =>
  apply mk

def mk_rel [SemiringOps R] [IsSemiring R] (w: r x y) : mk r x = mk r y := Quot.sound (RingCon.Generator.of w)
def of_mk_rel [SemiringOps R] [IsSemiring R] : mk r x = mk r y -> RingCon.generate r x y := Quotient.exact
def mk_surj [SemiringOps R] [IsSemiring R] : Function.Surjective (mk r) := by
  intro a
  induction a with | mk a =>
  exists a

private def preLift [SemiringOps R] [IsSemiring R] [SemiringOps T] [IsSemiring T] {r : R → R → Prop} {f : R →+* T} (h : ∀ ⦃x y⦄, r x y → f x = f y) : RingQuot r →+* T where
  toFun := by
    refine  Quotient.lift f ?_
    intro a b g
    induction g with
    | of =>
      apply h
      assumption
    | refl => rfl
    | symm => symm; assumption
    | trans _ _ ih₀ ih₁ => rw [ih₀, ih₁]
    | add =>
      rw [map_add, map_add]
      congr
    | mul =>
      rw [map_mul, map_mul]
      congr
  map_zero := map_zero f
  map_one := map_one f
  map_add := by
    intro a b
    induction a; induction b
    apply map_add
  map_mul := by
    intro a b
    induction a; induction b
    apply map_mul

def lift [SemiringOps R] [IsSemiring R] [SemiringOps T] [IsSemiring T]: {f: R →+* T // ∀ ⦃x y⦄, r x y → f x = f y } ≃ (RingQuot r →+* T) where
  toFun f := preLift f.property
  invFun f := {
    val := f.comp (mk r)
    property := by
      intro x y h
      show f (mk r x) = f (mk r y)
      congr 1; apply mk_rel
      assumption
  }
  leftInv _ := rfl
  rightInv f := by
    ext x; induction x
    rfl

@[simp]
def lift_mk_apply [SemiringOps R] [IsSemiring R] [SemiringOps T] [IsSemiring T] (f : R →+* T) {r : R → R → Prop} (w : ∀ ⦃x y⦄, r x y → f x = f y) (x) :
    lift ⟨f, w⟩ (mk r x) = f x := rfl

variable (S: Type*) [SemiringOps S] [SemiringOps R] [IsSemiring R] [IsSemiring S] [SMul S R] [AlgebraMap S R] [IsAlgebra S R]
   [SemiringOps A] [IsSemiring A] [AlgebraMap S A] [SMul S A] [IsAlgebra S A]
   [SemiringOps B] [IsSemiring B] [AlgebraMap S B] [SMul S B] [IsAlgebra S B]

def mkAlgHom (r: R -> R -> Prop) : R →ₐ[S] RingQuot r where
  toFun := mk _
  map_add := map_add _
  map_mul := map_mul _
  map_algebraMap _ := rfl

def indAlg {motive: RingQuot r -> Prop} (mk: ∀x, motive (mkAlgHom S r x)) : ∀q, motive q := by
  intro q
  induction q using AlgQuotient.ind with
  | mk a =>
  apply mk

def mkAlgHom_rel {s : A → A → Prop} {x y : A} (w : s x y) :
    mkAlgHom S s x = mkAlgHom S s y := mk_rel w

def mkAlgHom_surj (r: R -> R -> Prop) : Function.Surjective (mkAlgHom S r) := mk_surj

private def preLiftAlgHom {s : A → A → Prop} {f : A →ₐ[S] B }
  (h : ∀ ⦃x y⦄, s x y → f x = f y) : RingQuot s →ₐ[S] B := {
    preLift (f := f.toRingHom) h with
    map_algebraMap := map_algebraMap f
  }

def liftAlgHom {s : A → A → Prop} : { f : A →ₐ[S] B // ∀ ⦃x y⦄, s x y → f x = f y } ≃ (RingQuot s →ₐ[S] B) where
  toFun f := preLiftAlgHom S f.property
  invFun f := {
    val := {
      (lift.symm f.toRingHom).val with
      map_algebraMap := map_algebraMap f
    }
    property := by
      intro x y h
      simp
      show f (mk _ _) = f (mk _ _)
      congr 1; apply mk_rel
      assumption
  }
  leftInv _ := rfl
  rightInv f := by
    ext x; induction x
    rfl

@[simp]
def liftAlgHom_mkAlgHom_apply (f : A →ₐ[S] B) {s : A → A → Prop}
    (w : ∀ ⦃x y⦄, s x y → f x = f y) (x) : (liftAlgHom S ⟨f, w⟩) ((mkAlgHom S s) x) = f x := rfl

@[ext 1100]
def ringQuot_ext {s : A → A → Prop} (f g : RingQuot s →ₐ[S] B)
    (w : f.comp (mkAlgHom S s) = g.comp (mkAlgHom S s)) : f = g := by
  apply DFunLike.ext
  intro x
  rcases mkAlgHom_surj S s x with ⟨x, rfl⟩
  show (f.comp (mkAlgHom S s)) x = _
  rw [w]; rfl

def ringQuot_ext'
  {s : A → A → Prop} (f g : RingQuot s →ₐ[S] B)
  (w : f.comp (RingQuot.mkAlgHom S s) = g.comp (RingQuot.mkAlgHom S s)) : f = g := by
  ext
  rw [w]

attribute [irreducible] RingQuot instSemiringOps instRingOps mk lift liftAlgHom

end RingQuot
