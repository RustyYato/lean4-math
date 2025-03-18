import Math.Data.Poly.Dvd
import Math.Data.Poly.Eval
import Math.Algebra.Ring.Theory.RMod.Poly

open Poly

def GaussianInteger : Type := RMod (α := ℤ[X]) (X ^ 2 + 1)

namespace GaussianInteger

instance : RingOps GaussianInteger := RMod.instRingOps
instance : IsRing GaussianInteger := RMod.instRing
instance : IsCommMagma GaussianInteger := RMod.instCommMagma
instance : AlgebraMap ℤ[X] GaussianInteger := RMod.instAlgMap
instance : SMul ℤ[X] GaussianInteger := RMod.isntSMul
instance : IsAlgebra ℤ[X] GaussianInteger := RMod.instAlgebra

scoped notation "ℤ[i]" => GaussianInteger

def induction' {motive : GaussianInteger -> Prop} (mk: ∀x: ℤ[X], motive (algebraMap x)) : ∀q, motive q := by
  intro r
  induction r using Quotient.ind
  apply mk

abbrev char : ℤ[X] := (X^2 + 1)

instance : IsInvertible (char.toFinsupp char.degreeNat) :=
  inferInstanceAs (IsInvertible 1)

-- the imaginary unit
def i: ℤ[i] := algebraMap (X: ℤ[X])

def i_sq : i ^ 2 = -1 := by
  refine neg_eq_of_add_right ?_
  apply RMod.map_eq_zero

def i_unit : Units ℤ[i] where
  val := i
  inv := -i
  val_mul_inv := by rw [←neg_mul_right, ←npow_two, i_sq, neg_neg]
  inv_mul_val := by rw [←neg_mul_left, ←npow_two, i_sq, neg_neg]

def i_isunit : IsUnit i where
  eq_unit := ⟨i_unit, rfl⟩

def real_ (x: GaussianInteger) : ℤ := (RMod.modPoly inferInstance x).toFinsupp 0
def img_ (x: GaussianInteger) : ℤ := (RMod.modPoly inferInstance x).toFinsupp 1

structure Real where
structure Img where

def real : Real := Real.mk
def img : Img := Img.mk

instance : FunLike Real GaussianInteger ℤ where
  coe _ := real_
  coe_inj _ _ _ := rfl
instance : FunLike Img GaussianInteger ℤ where
  coe _ := img_
  coe_inj _ _ _ := rfl

@[simp] def apply_real (r: Real) (x: GaussianInteger) : r x = real_ x := rfl
@[simp] def apply_img (i: Img) (x: GaussianInteger) : i x = img_ x := rfl

instance : IsZeroHom Real GaussianInteger ℤ where
  resp_zero _ := by
    simp [RMod.modPoly_zero, real_]
    rfl

instance : IsOneHom Real GaussianInteger ℤ where
  resp_one _ := by
    simp
    erw [real_, RMod.modPoly_const]
    rfl
    decide

instance : IsAddHom Real GaussianInteger ℤ where
  resp_add r := by
    intro x y
    induction x using induction' with | mk x =>
    induction y using induction' with | mk y =>
    show (Poly.mod (x + y) _ (inv := _)).toFinsupp 0 =
      (Poly.mod x _ (inv := _)).toFinsupp 0 +
      (Poly.mod y _ (inv := _)).toFinsupp 0
    sorry

instance : IsZeroHom Img GaussianInteger ℤ where
  resp_zero _ := by
    simp [RMod.modPoly_zero, img_]
    rfl

instance : IsAddHom Img GaussianInteger ℤ where
  resp_add _ := by
    intro x y
    simp [RMod.modPoly_zero, img_]
    rfl

def basis (x: ℤ[i]) : ∃(a b: ℤ), x = a + b * i := by

  sorry

end GaussianInteger
