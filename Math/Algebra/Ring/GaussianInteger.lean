import Math.Data.Poly.Basic
import Math.Algebra.Ring.Theory.Ideal.TwoSided.Quotient
import Math.Algebra.Ring.Theory.Ideal.TwoSided.Lattice

open Poly

def xsq_p1_ideal : Ideal (Poly ℤ) where
  carrier := Set.mk fun x => (X ^ 2 + 1) ∣ x
  mem_zero' := by
    rw [Set.mk_mem]
    apply dvd_zero
  mem_add' {a b} ha hb := by
    rw [Set.mk_mem]
    apply dvd_add <;> assumption
  mem_neg' {a} ha := by
    rw [Set.mk_mem]
    apply dvd_neg.mp <;> assumption
  mem_mul_left' r {x} hx := by
    rw [Set.mk_mem]
    apply dvd_trans
    apply hx
    exact dvd_mul_right x r
  mem_mul_right' r {x} hx := by
    rw [Set.mk_mem]
    apply dvd_trans
    apply hx
    exact dvd_mul_left x r

@[simp]
def mem_xsq_p1_ideal (p: ℤ[X]) : p ∈ xsq_p1_ideal ↔ X ^ 2 + 1 ∣ p := by
  simp [xsq_p1_ideal, Membership.mem, SetLike.coe]

def xsq_p1_ideal_spec: xsq_p1_ideal = Ideal.generate {X^2+1} := by
  ext p
  apply Iff.intro
  · intro h
    simp at h
    obtain ⟨k, rfl⟩ := h
    apply mem_mul_right
    apply Ideal.Generate.of
    rfl
  · intro h
    apply Ideal.of_mem_generate _ _ _ _ h
    rintro x rfl
    simp
    apply dvd_refl

def GaussianInteger : Type := xsq_p1_ideal.toRing

namespace GaussianInteger

instance : RingOps GaussianInteger :=
  inferInstanceAs (RingOps xsq_p1_ideal.toRing)
instance : IsRing GaussianInteger :=
  inferInstanceAs (IsRing xsq_p1_ideal.toRing)

scoped notation "ℤ[i]" => GaussianInteger

-- the imaginary unit
def i: ℤ[i] := xsq_p1_ideal.mkQuot X

def i_sq : i ^ 2 = -1 := by
  refine neg_eq_of_add_right ?_
  apply Quotient.sound
  rw [one_mul, ←npow_two]
  show _ - 0 ∈ _
  rw [sub_zero]
  simp [xsq_p1_ideal, Membership.mem, SetLike.coe]
  apply dvd_refl

def i_unit : Units ℤ[i] where
  val := i
  inv := -i
  val_mul_inv := by rw [←neg_mul_right, ←npow_two, i_sq, neg_neg]
  inv_mul_val := by rw [←neg_mul_left, ←npow_two, i_sq, neg_neg]

def i_isunit : IsUnit i where
  eq_unit := ⟨i_unit, rfl⟩

def basis (x: ℤ[i]) : ∃(a b: ℤ), x = a + b * i := by
  sorry

end GaussianInteger
