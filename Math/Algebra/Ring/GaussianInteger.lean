import Math.Data.Poly.Dvd
import Math.Data.Poly.Basic
import Math.Algebra.Ring.Theory.RMod.Poly
import Math.Algebra.AddGroupWithOne.Hom

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

instance : IsInvertible char.lead := inferInstanceAs (IsInvertible 1)

-- the imaginary unit
def i: ℤ[i] := algebraMap (X: ℤ[X])

def i_sq : i ^ 2 = -1 := by
  refine neg_eq_of_add_right ?_
  apply RMod.map_eq_zero

def i_mul_i : i * i = -1 := by
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
    rw [Poly.add_mod]
    rfl

instance : IsZeroHom Img GaussianInteger ℤ where
  resp_zero _ := by
    simp [RMod.modPoly_zero, img_]
    rfl

instance : IsAddHom Img GaussianInteger ℤ where
  resp_add _ := by
    intro x y
    induction x using induction' with | mk x =>
    induction y using induction' with | mk y =>
    show (Poly.mod (x + y) _ (inv := _)).toFinsupp 1 =
      (Poly.mod x _ (inv := _)).toFinsupp 1 +
      (Poly.mod y _ (inv := _)).toFinsupp 1
    rw [Poly.add_mod]
    rfl

def char_degree_eq : char.degree = .of 2 := rfl

private def basis_mod (a b: ℤ) : (a + b * (X: ℤ[X])).mod char = a + b * (X: ℤ[X]) := by
  rw [mod_of_lt]
  show _ < (X ^ 2 + C 1).degree
  refine if h:a = 0 ∧ b = 0  then ?_ else ?_
  obtain ⟨hr, hi⟩ := h
  rw [hr, hi]
  rw [intCast_zero]
  simp
  apply WithBot.LT.bot
  rw [Poly.add_degree_of_ne_degree, Poly.add_degree_of_ne_degree, Poly.Xpow_degree, Poly.const_degree_ne_zero]
  rw (occs := [2]) [max_iff_le_right.mp]
  rw [Poly.mul_degree, ←npow_one X, Poly.Xpow_degree]
  rw [max_lt_iff]
  apply And.intro
  rw [←resp_intCast (Poly.C (P := ℤ)), Poly.const_degree_eq]
  split
  apply WithBot.LT.bot
  any_goals decide
  rw [←resp_intCast (Poly.C (P := ℤ)), Poly.const_degree_eq]
  split
  apply WithBot.LT.bot
  apply WithBot.LT.of
  decide
  rw [←resp_intCast (Poly.C (P := ℤ)), Poly.const_degree_eq]
  split
  rw [Poly.mul_degree, ←resp_intCast (Poly.C (P := ℤ)), Poly.const_degree_ne_zero,
    ←npow_one X, Poly.Xpow_degree]
  decide
  intro g
  rename_i h'
  apply h; apply And.intro
  exact h'
  exact g
  rw [mul_degree, ←resp_intCast (Poly.C (P := ℤ)), Poly.const_degree_eq, ←npow_one X, Poly.Xpow_degree]
  split
  decide
  decide

def basis (x: ℤ[i]) : x = real x + img x * i := by
  induction x using induction' with | mk x =>
  apply Quotient.sound
  show char ∣ _
  unfold char
  let r := (Poly.mod x char).toFinsupp 0
  let i := (Poly.mod x char).toFinsupp 1
  show _ ∣ x - ((r: ℤ[X]) + (i: ℤ[X]) * X)
  apply (Poly.mod_eq_iff_sub_dvd _ _ (inv := inferInstance)).mpr
  rw [basis_mod]
  ext n
  show _ = (r: ℤ[X]).toFinsupp n + ((i: ℤ[X]) * X).toFinsupp n
  match n with
  | 0 =>
    rw [coeff_mul_X_zero, add_zero]
    rfl
  | 1 =>
    erw [coeff_mul_X_succ]
    symm; apply zero_add
  | n + 2 =>
    erw [zero_add]
    show (x.mod char).toFinsupp _ = 0
    rw [Poly.of_degree_lt]
    apply lt_of_lt_of_le
    apply Poly.mod_degree_lt
    rw [char_degree_eq]
    apply WithBot.LE.of
    exact Nat.le_add_left 2 n

def induction {motive: ℤ[i] -> Prop} : (mk: ∀real img: ℤ, motive (real + img * i)) -> ∀x, motive x := by
  intro h x
  rw [x.basis]
  apply h

@[ext]
def ext (a b: ℤ[i]) : real a = real b -> img a = img b -> a = b := by
  intro hr hi
  rw [a.basis, b.basis, hr, hi]

def basis_mul (a b c d: ℤ) : (a + b * i) * (c + d * i) = (a * c - b * d: ℤ) + (a * d + b * c: ℤ) * i := by
  rw [mul_add, add_mul, add_mul]
  ac_nf
  rw [←mul_assoc, i_mul_i, ←neg_mul_left, one_mul]
  rw [add_comm, add_assoc, add_assoc, ←sub_eq_add_neg, ←add_assoc, ←mul_add,
    mul_comm, add_comm]
  simp [intCast_mul, intCast_add, intCast_sub]
  ac_rfl

instance : HasChar ℤ[i] 0 := HasChar.of_ring_emb {
  algebraMap (R := ℤ) (A := ℤ[i]) with
  inj' := by
    intro a b eq
    replace eq : (a: ℤ[i]) = b := eq
    have : real b = b := by
      rw [resp_intCast]
      rfl
    rw [←eq, resp_intCast] at this
    assumption
}

def basis_real (a b: ℤ) : real (a + b * i) = a := by
  show (Poly.mod _ _).toFinsupp 0 = _
  rw [basis_mod]
  show a + _ = _
  rw (occs := [2]) [←add_zero a]
  congr
  rw [coeff_mul_X_zero]

def basis_img (a b: ℤ) : img (a + b * i) = b := by
  show (Poly.mod _ _).toFinsupp 1 = _
  rw [basis_mod]
  show (a: ℤ[X]).toFinsupp 1 + _ = _
  rw (occs := [2]) [←zero_add b]
  congr
  rw [coeff_mul_X_succ]
  rfl

end GaussianInteger
--
