import Math.Data.Poly.Eval
-- import Math.Algebra.Ring.Theory.Ideal.TwoSided.Quotient
-- import Math.Algebra.Ring.Theory.Ideal.TwoSided.Lattice
import Math.Algebra.Ring.Theory.RMod.Basic

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

private def clock (i: ℕ) : ℤ :=
  match h:i % 4 with
  | 0 => 1
  | 1 => 0
  | 2 => -1
  | 3 => 0
  | n + 4 => by
    have h : i % 4 = n + 4 := h
    have := Nat.mod_lt i (y := 4) (by decide)
    rw [h] at this
    omega

def real : GaussianInteger →+* ℤ where
  toFun := by
    -- FIXME: eval doesn't work, need to go back to explicit sum
    -- or define the quotient and remainder of a polynomial
    -- (this will likely prove more useful)
    refine Quotient.lift (fun x: ℤ[X] => x.eval 0) ?_
    intro a b eq
    dsimp
    replace eq : X^2 + 1 ∣ a - b := eq
    apply eq_of_sub_eq_zero
    show a.evalHom (0: ℤ) - b.evalHom (0: ℤ) = 0
    rw [←resp_sub]
    induction a generalizing b with
    | const a =>
      induction b with
      | const b =>
        rw [←resp_sub] at eq
        obtain ⟨k, eq⟩ := eq
        rw [add_mul, one_mul, X_npow_mul_eq_mul_X_npow] at eq
        cases k with | mul_add k₀ k =>
        rw [add_mul] at eq
        sorry
      | mul_add b b₀ b_ne_zero ih₀ ih =>
        simp [resp_sub, resp_add]
        sorry
    | mul_add a a₀ a_ne_zero ih₀ ih =>
      sorry
  resp_zero := sorry
  resp_one := sorry
  resp_add := sorry
  resp_mul := sorry

def basis (x: ℤ[i]) : ∃(a b: ℤ), x = a + b * i := by

  sorry

end GaussianInteger
