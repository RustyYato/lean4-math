import Math.Data.Complex.Defs
import Math.Algebra.Ring.Theory.RMod.Poly
import Math.Algebra.AddGroupWithOne.Hom
import Math.Data.Poly.Prime
import Math.Data.Poly.Dvd
import Math.Data.Poly.Eval

open Poly Classical

def Complex.charPoly : ℝ[X] := X ^ 2 + 1
def Complex.charPoly.degree : charPoly.degree = .of 2 := by
  unfold charPoly
  rw [add_degree_of_ne_degree, Xpow_degree, ←map_one C, const_degree_ne_zero]
  rfl
  symm; apply zero_ne_one
  rw [Xpow_degree, ←map_one C, const_degree_ne_zero]
  trivial
  symm; apply zero_ne_one

noncomputable instance : IsInvertible Complex.charPoly.lead where
  invOf := 1
  mul_invOf := by
    rw [lead, degreeNat, Complex.charPoly.degree]
    rfl
  invOf_mul := by
    rw [lead, degreeNat, Complex.charPoly.degree]
    rfl

-- the complex numbers defined as the ring generated by a certain ideal
def Complex' : Type := RMod Complex.charPoly

namespace Complex'

scoped notation "ℝ[i]" => Complex'

instance : RingOps ℝ[i] := RMod.instRingOps
instance : IsRing ℝ[i] := RMod.instRing
instance : IsCommMagma ℝ[i] := RMod.instCommMagma
instance : AlgebraMap ℝ[X] ℝ[i] := RMod.instAlgMap
instance : SMul ℝ[X] ℝ[i] := RMod.isntSMul
instance : IsAlgebra ℝ[X] ℝ[i] := RMod.instAlgebra

instance : AlgebraMap ℝ ℝ[i] := AlgebraMap.ofHom (algebraMap.comp Poly.C.toHom)
instance : SMul ℝ ℝ[i] where
  smul r x := algebraMap r * x
instance : IsAlgebra ℝ ℝ[i] where
  commutes _ _ := by rw [mul_comm]
  smul_def _ _ := rfl
instance : Coe ℝ ℝ[i] where
  coe := algebraMap

def induction' {motive : ℝ[i] -> Prop} (mk: ∀x: ℝ[X], motive (algebraMap x)) : ∀q, motive q := by
  intro r
  induction r using Quotient.ind
  apply mk

-- the imaginary unit
def i: ℝ[i] := algebraMap (X: ℝ[X])

def i_sq : i * i = -1 := by
  refine neg_eq_of_add_right ?_
  apply RMod.map_eq_zero

@[simp]
def ofComplex (c: ℂ) : ℝ[i] := c.real + c.img * i

def eval_eq_mod_eval (p: ℝ[X]) : (Poly.eval Complex.i) p = (Poly.eval Complex.i) (p.mod Complex.charPoly) := by
  rw (occs := [1]) [←p.div_mul_add_mod Complex.charPoly]
  rw [eval_add]; rw (occs := [3]) [←zero_add (eval _ _)]
  congr
  rw [eval_mul]
  rw [show (eval Complex.i Complex.charPoly = 0) from ?_, mul_zero]
  unfold Complex.charPoly
  rw [eval_add, Xpow_eq_monomial, eval_monomial, eval_one]
  rfl

def toComplex : ℝ[i] -> ℂ := by
  apply Quotient.lift (Poly.eval Complex.i)
  intro a b eq
  replace eq : Complex.charPoly ∣ _ := eq
  rw [eval_eq_mod_eval, eval_eq_mod_eval b]
  congr 1
  refine (mod_eq_iff_sub_dvd a b).mp ?_
  assumption

def algMap_charPoly : algebraMap Complex.charPoly = (0: ℝ[i]) := by
  apply Quotient.sound
  show Complex.charPoly ∣ _
  rw [sub_zero]

def rightInv : Function.IsRightInverse toComplex ofComplex := by
  intro r
  induction r using induction' with | mk r =>
  unfold toComplex
  show ofComplex (eval _ _) = _
  rw [eval_eq_mod_eval]
  let r' := eval Complex.i (r.mod Complex.charPoly)
  show ofComplex r' = _

  rw [←r.div_mul_add_mod Complex.charPoly (inv := inferInstance),
    map_add, map_mul, algMap_charPoly, mul_zero, zero_add]
  unfold r'; clear r'
  have ⟨a, b, eq⟩ := eq_linear_of_deg_lt_2 (r.mod Complex.charPoly) ?_
  rw [eq]; clear eq r
  simp [eval_add, eval_mul, eval_C, eval_X]
  rw [map_add, map_mul]
  rfl
  rw [←Complex.charPoly.degree]
  apply mod_degree_lt

def equivComplex : ℂ ≃+* ℝ[i] where
  toFun := ofComplex
  invFun := toComplex
  leftInv := by
    intro c
    simp
    show eval _ _ = _
    simp
    show eval Complex.i (Poly.C c.real + Poly.C c.img * X) = _
    rw [eval_add, eval_mul, eval_X, eval_C, eval_C]
    ext <;> simp
  rightInv := by
    apply rightInv
  map_zero := by simp [map_zero]
  map_one := by simp [map_zero, map_one]
  map_add {x y} := by simp [map_add, add_mul]; ac_rfl
  map_mul {x y} := by
    simp [map_add, map_mul, map_sub, add_mul, mul_add]
    repeat first|rw [add_assoc]|rw [mul_assoc]
    rw [mul_left_comm i, i_sq]
    rw (occs := [2]) [add_comm (algebraMap x.real * _)]
    rw [add_assoc, add_assoc, mul_neg, mul_neg, mul_one]
    rw [add_comm (-_), sub_eq_add_neg]
    ac_nf

end Complex'
