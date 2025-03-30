import Math.Data.Poly.Dvd
import Math.Data.Poly.Prime
import Math.Data.Poly.Basic
import Math.Algebra.Ring.Theory.RMod.Poly
import Math.Algebra.AddGroupWithOne.Hom
import Math.Data.Int.Basic

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
def char_degree : char.degree = .of 2 := rfl

instance : IsInvertible char.lead := inferInstanceAs (IsInvertible 1)
instance : IsInvertible (X^2+1: ℤ[X]).lead := inferInstanceAs (IsInvertible 1)

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

def real : ℤ[i] →+₁ ℤ where
  toFun x := (RMod.modPoly inferInstance x).toFinsupp 0
  map_zero := by
    simp [RMod.modPoly_zero]
    rfl
  map_one := by
    simp
    erw [RMod.modPoly_const]
    rfl
    trivial
  map_add {x y} := by
    induction x using induction' with | mk x =>
    induction y using induction' with | mk y =>
    show (Poly.mod (x + y) _ (inv := _)).toFinsupp 0 =
      (Poly.mod x _ (inv := _)).toFinsupp 0 +
      (Poly.mod y _ (inv := _)).toFinsupp 0
    rw [Poly.add_mod]
    rfl

def img : ℤ[i] →+ ℤ where
  toFun x := (RMod.modPoly inferInstance x).toFinsupp 1
  map_zero := by
    simp [RMod.modPoly_zero]
    rfl
  map_add {x y} := by
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
  rw [←map_intCast (Poly.C (P := ℤ)), Poly.const_degree_eq]
  split
  apply WithBot.LT.bot
  any_goals decide
  rw [←map_intCast (Poly.C (P := ℤ)), Poly.const_degree_eq]
  split
  apply WithBot.LT.bot
  apply WithBot.LT.of
  decide
  rw [←map_intCast (Poly.C (P := ℤ)), Poly.const_degree_eq]
  split
  rw [Poly.mul_degree, ←map_intCast (Poly.C (P := ℤ)), Poly.const_degree_ne_zero,
    ←npow_one X, Poly.Xpow_degree]
  decide
  intro g
  rename_i h'
  apply h; apply And.intro
  exact h'
  exact g
  rw [mul_degree, ←map_intCast (Poly.C (P := ℤ)), Poly.const_degree_eq, ←npow_one X, Poly.Xpow_degree]
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

@[induction_eliminator]
def induction {motive: ℤ[i] -> Prop} : (mk: ∀real img: ℤ, motive (real + img * i)) -> ∀x, motive x := by
  intro h x
  rw [x.basis]
  apply h

@[ext]
def ext (a b: ℤ[i]) : real a = real b -> img a = img b -> a = b := by
  intro hr hi
  rw [a.basis, b.basis, hr, hi]

@[simp]
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
      rw [map_intCast]
      rfl
    rw [←eq, map_intCast] at this
    assumption
}

@[simp]
def basis_real (a b: ℤ) : real (a + b * i) = a := by
  show (Poly.mod _ _).toFinsupp 0 = _
  rw [basis_mod]
  show a + _ = _
  rw (occs := [2]) [←add_zero a]
  congr
  rw [coeff_mul_X_zero]

@[simp]
def basis_img (a b: ℤ) : img (a + b * i) = b := by
  show (Poly.mod _ _).toFinsupp 1 = _
  rw [basis_mod]
  show (a: ℤ[X]).toFinsupp 1 + _ = _
  rw (occs := [2]) [←zero_add b]
  congr
  rw [coeff_mul_X_succ]
  rfl

instance : Repr ℤ[i] where
  reprPrec x _ :=
    if img x = 0 then
      reprStr (real x)
    else if real x = 0 then
      if img x = 1 then
        "i"
      else
        reprStr (img x) ++ " i"
    else
      reprStr (real x) ++ " + " ++ (if img x = 1 then "" else reprStr (img x)) ++ " i"

instance : DecidableEq ℤ[i] :=
  fun a b =>
  decidable_of_decidable_of_iff (p := real a = real b ∧ img a = img b) <| by
    induction a; induction b
    simp
    rename_i a b c d
    apply Iff.intro
    intro ⟨rfl, rfl⟩
    rfl
    intro h
    have : real (c + d * i) = c := by simp
    rw [←h] at this
    simp at this
    have : img (c + d * i) = d := by simp
    rw [←h] at this
    simp at this
    trivial

@[simp]
def real_zero : real 0 = 0 := by
  rw [show (0 = (0: ℤ) + (0: ℤ) * i) by simp [intCast_zero], basis_real]

@[simp]
def img_zero : img 0 = 0 := by
  rw [show (0 = (0: ℤ) + (0: ℤ) * i) by simp [intCast_zero], basis_img]

@[simp]
def real_one : real 1 = 1 := by
  rw [show (1 = (1: ℤ) + (0: ℤ) * i) by simp [intCast_one, intCast_zero], basis_real]

@[simp]
def img_one : img 1 = 0 := by
  rw [show (1 = (1: ℤ) + (0: ℤ) * i) by simp [intCast_one, intCast_zero], basis_img]

def conj (a: ℤ[i]) : ℤ := real a - img a
def norm_sq : ℤ[i] →*₀ ℤ where
  toFun a := real a * real a + img a * img a
  map_zero := by simp
  map_one := by simp
  map_mul := by
    intro x y
    induction x with | mk a b =>
    induction y with | mk c d =>
    simp only [mul_sub, sub_mul, mul_add, add_mul]
    ac_nf
    simp [←mul_assoc, i_mul_i, ←neg_mul_left, one_mul]
    simp [mul_assoc i]
    norm_cast
    ac_nf
    rw [←mul_add i, mul_comm i]
    simp only [←add_assoc]
    norm_cast
    simp
    rw [add_comm _ (a * c)]
    simp only [mul_add, add_mul]
    simp only [←neg_mul_left, ←neg_mul_right]
    rw [neg_neg]
    ac_nf
    generalize a * (b * (c * d)) = x
    generalize a * (a * (c * c)) = ac
    generalize b * (b * (c * c)) = bc
    ac_nf
    iterate 2 rw [add_left_comm _ (-x)]
    rw [←add_assoc x (-x), add_neg_cancel, zero_add]
    iterate 2 rw [add_left_comm _ (-x)]
    rw [←add_assoc x (-x), add_neg_cancel, zero_add]

@[simp]
def apply_norm_sq : norm_sq a = real a * real a + img a * img a := rfl

def norm_sq_eq_zero : norm_sq a = 0 ↔ a = 0 := by
  apply flip Iff.intro
  rintro rfl; rw [map_zero]
  intro h
  induction a with | mk a b =>
  replace h : a * a + b * b = 0 := by simpa using h
  ext <;> simp
  apply Int.eq_zero_of_sq_eq_zero
  apply le_antisymm
  rw [neg_eq_of_add_right h]
  refine Int.neg_le_zero_iff.mpr ?_
  exact Int.sq_nonneg b
  exact Int.sq_nonneg a
  apply Int.eq_zero_of_sq_eq_zero
  apply le_antisymm
  rw [←neg_eq_of_add_left h]
  refine Int.neg_le_zero_iff.mpr ?_
  exact Int.sq_nonneg a
  exact Int.sq_nonneg b

def of_basis_eq_zero {a b: ℤ} : a + b * i = 0 -> a = 0 ∧ b = 0 := by
  intro h
  have ha : real (a + b * i) = a := by simp
  rw [h] at ha
  have hb : img (a + b * i) = b := by simp
  rw [h] at hb
  simp at ha hb
  rw [←ha, ←hb]
  trivial

instance : NoZeroDivisors ℤ[i] where
  of_mul_eq_zero {x y} := by
    intro h
    have : norm_sq (x * y) = 0 := by rw [h, map_zero]
    rw [map_mul] at this
    rcases of_mul_eq_zero this with g | g
    left; rwa [norm_sq_eq_zero] at g
    right; rwa [norm_sq_eq_zero] at g

def is_prime_ideal : (Ideal.of_dvd char).IsPrime := by
  refine (Ideal.prime_iff_no_zero_divisors (Ideal.of_dvd char)).mpr ?_
  exact inferInstanceAs (NoZeroDivisors ℤ[i])

end GaussianInteger
--
