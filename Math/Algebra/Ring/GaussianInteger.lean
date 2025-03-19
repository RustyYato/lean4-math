import Math.Data.Poly.Dvd
import Math.Data.Poly.Prime
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
  resp_zero := by
    simp [RMod.modPoly_zero]
    rfl
  resp_one := by
    simp
    erw [RMod.modPoly_const]
    rfl
    trivial
  resp_add {x y} := by
    induction x using induction' with | mk x =>
    induction y using induction' with | mk y =>
    show (Poly.mod (x + y) _ (inv := _)).toFinsupp 0 =
      (Poly.mod x _ (inv := _)).toFinsupp 0 +
      (Poly.mod y _ (inv := _)).toFinsupp 0
    rw [Poly.add_mod]
    rfl

def img : ℤ[i] →+ ℤ where
  toFun x := (RMod.modPoly inferInstance x).toFinsupp 1
  resp_zero := by
    simp [RMod.modPoly_zero]
    rfl
  resp_add {x y} := by
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
      rw [resp_intCast]
      rfl
    rw [←eq, resp_intCast] at this
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

def is_prime_ideal : (Ideal.of_dvd char).IsPrime := by
  apply Poly.is_prime_ideal
  intro a b anez bnez ha hb aleb h
  rw [char_degree] at ha hb
  unfold char at *
  match hadeg:a.degree, hbdeg:b.degree with
  | .of (adeg + 2), _ =>
    rw [hadeg] at ha
    cases ha
    contradiction
  | _, .of (bdeg + 2) =>
    rw [hbdeg] at hb
    cases hb
    contradiction
  | ⊥, _ => contradiction
  | _, ⊥ => contradiction
  | .of 1, .of 0 =>
    rw [hadeg, hbdeg] at aleb
    contradiction
  | .of 0, .of 0 =>
    clear anez bnez
    obtain ⟨a, rfl, anez⟩ := a.eq_C_of_deg_eq_0 hadeg
    obtain ⟨b, rfl, bnez⟩ := b.eq_C_of_deg_eq_0 hbdeg
    rw [←resp_mul] at h
    rw [mod_eq_zero_iff_dvd (inv := inferInstance), mod_of_lt] at h
    rw [←resp_zero C] at h
    cases of_mul_eq_zero (C.inj h) <;> contradiction
    rw [char_degree]
    rw [const_degree_eq]; split
    apply WithBot.LT.bot
    simp
  | .of 0, .of 1 =>
    clear anez bnez
    obtain ⟨a, rfl, anez⟩ := a.eq_C_of_deg_eq_0 hadeg
    obtain ⟨b₀, b₁, rfl, bnez⟩ := b.eq_linear_of_deg_eq_1 hbdeg
    rw [mod_eq_zero_iff_dvd (inv := inferInstance), mod_of_lt] at h
    replace h := of_mul_eq_zero h
    rcases h with h | h
    rw [←resp_zero C, C.inj.eq_iff] at h
    contradiction
    rw [show 0 = 0 * (X: ℤ[X]) + C 0 by simp [resp_zero], add_comm] at h
    replace ⟨h, _⟩ := mul_X_add_C_inj h
    rw [←resp_zero C] at h
    have := C.inj h
    contradiction
    rw [mul_add, ←resp_mul, ←mul_assoc, ←resp_mul]
    apply lt_of_le_of_lt
    apply add_degree
    rw [char_degree, const_degree_eq]
    split
    rw [max_iff_le_left.mp]
    rw [mul_degree, const_degree_eq, X_degree]
    split
    apply WithBot.LT.bot
    decide
    apply bot_le
    simp
    rw [const_degree_eq]
    split
    decide
    decide
  | .of 1, .of 1 =>
    sorry

instance : NoZeroDivisors ℤ[i] := (Ideal.prime_iff_no_zero_divisors _).mp is_prime_ideal

end GaussianInteger
--
