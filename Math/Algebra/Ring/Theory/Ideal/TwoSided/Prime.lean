import Math.Data.List.Algebra
import Math.Algebra.Dvd
import Math.Algebra.Ring.Theory.Ideal.TwoSided.Lattice
import Math.Algebra.Ring.Theory.Ideal.TwoSided.Quotient

namespace Ideal

variable [RingOps α] [IsRing α]

def IsPrime (i: Ideal α) : Prop := ∀a b: α, a * b ∈ i -> a ∈ i ∨ b ∈ i

def prime_iff_no_zero_divisors (i: Ideal α) : i.IsPrime ↔ NoZeroDivisors i.toRing := by
  apply Iff.intro
  · intro h
    refine ⟨?_⟩
    intro a b g
    induction a with | mk a =>
    induction b with | mk b =>
    rw [←resp_mul] at g
    simp [i.mkQuot_eq_zero_iff] at *
    exact h a b g
  · intro ⟨h⟩
    intro a b g
    simp [←i.mkQuot_eq_zero_iff] at *
    rw [resp_mul] at g
    exact h g

end Ideal
