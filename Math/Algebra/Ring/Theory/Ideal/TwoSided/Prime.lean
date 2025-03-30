import Math.Data.List.Algebra
import Math.Algebra.Dvd
import Math.Algebra.Ring.Theory.Ideal.TwoSided.Lattice
import Math.Algebra.Ring.Theory.Ideal.TwoSided.Quotient

namespace Ideal

variable [RingOps R] [IsRing R]

def IsPrime (i: Ideal R) : Prop := ∀a b: R, a * b ∈ i -> a ∈ i ∨ b ∈ i

def prime_iff_no_zero_divisors (i: Ideal R) : i.IsPrime ↔ NoZeroDivisors i.toRing := by
  apply Iff.intro
  · intro h
    refine ⟨?_⟩
    intro a b g
    induction a with | mk a =>
    induction b with | mk b =>
    rw [←map_mul] at g
    simp [i.mkQuot_eq_zero_iff] at *
    exact h a b g
  · intro ⟨h⟩
    intro a b g
    simp [←i.mkQuot_eq_zero_iff] at *
    rw [map_mul] at g
    exact h g

def prime_iff_compl_subsemigroup (i: Ideal R) : i.IsPrime ↔ ∃m: Subsemigroup R, m.carrier = i.carrierᶜ := by
  apply Iff.intro
  · intro h
    refine ⟨{
      carrier := _
      mem_mul' := ?_
    } , rfl⟩
    · intro a b ha hb
      intro g
      cases h _ _ g <;> contradiction
  · intro ⟨⟨_, h⟩ , rfl⟩
    intro a b g
    have := (h · · g)
    simp [Set.mem_compl] at this
    exact Or.symm ((fun {a b} => Classical.or_iff_not_imp_right.mpr) this)

def prime_iff_compl_sumonoid (i: Ideal R) : i.IsPrime ∧ i < ⊤ ↔ ∃m: Submonoid R, m.carrier = i.carrierᶜ := by
  apply Iff.intro
  · intro ⟨h, proper⟩
    refine ⟨{
      carrier := _
      mem_one' := ?_
      mem_mul' := ?_
    } , rfl⟩
    · intro a b ha hb
      intro g
      cases h _ _ g <;> contradiction
    · intro g
      have := i.eq_univ_of_mem_unit 1 g
      subst i
      have := lt_irrefl proper
      contradiction
  · intro ⟨⟨⟨_, h₀⟩, h₁⟩ , rfl⟩
    apply And.intro
    intro a b g
    have := (h₀ · · g)
    simp [Set.mem_compl] at this
    exact Or.symm ((fun {a b} => Classical.or_iff_not_imp_right.mpr) this)
    apply lt_of_le_of_ne
    apply le_top
    rintro rfl
    simp at h₁
    apply h₁
    trivial

def prime_preimage [RingOps S] [IsRing S] (f: R →+* S) (i: Ideal S) : i.IsPrime -> (i.preimage f).IsPrime := by
  intro h a b eq
  apply h
  rw [←map_mul]
  assumption

end Ideal
