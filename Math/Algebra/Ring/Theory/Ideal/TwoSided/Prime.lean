import Math.Algebra.Ring.Theory.Ideal.TwoSided.Principal
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
      mem_mul := ?_
    } , rfl⟩
    · intro a b ha hb
      intro g
      cases h _ _ g <;> contradiction
  · intro ⟨⟨_, h⟩ , rfl⟩
    intro a b g
    have := (h · · g)
    simp [Set.mem_compl] at this
    exact Or.symm ((fun {a b} => Classical.or_iff_not_imp_right.mpr) this)

def prime_iff_compl_submonoid (i: Ideal R) : i.IsPrime ∧ i < ⊤ ↔ ∃m: Submonoid R, m.carrier = i.carrierᶜ := by
  apply Iff.intro
  · intro ⟨h, proper⟩
    refine ⟨{
      carrier := _
      mem_one := ?_
      mem_mul := ?_
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

def prime_of_maximal [IsCommMagma R] (m: Ideal R) (hm: m.isMaximal) : m.IsPrime := by
  open scoped IsLawfulDvd.ofMul in
  intro a b h
  apply Classical.or_iff_not_imp_left.mpr
  intro a_notin_m
  let i: Ideal R := m + principal a
  have m_lt_i : m < i := by
    apply And.intro
    apply le_max_left
    intro g
    have := g a ?_
    contradiction
    apply le_max_right (α := Ideal R)
    show a ∈ principal a
    rw [principal_eq_generate]
    apply Generate.of
    rfl
  have i_eq_top : i = ⊤ := hm.right i m_lt_i
  have : 1 ∈ i := by rw [i_eq_top]; trivial
  obtain ⟨⟨m', r'⟩, hm', hr', g⟩ := this
  simp at hm' hr' g
  rw [←of_dvd_eq_principal] at hr'
  obtain ⟨r, rfl⟩ := hr'
  have : b = m' * b + r * (a * b) := by
    rw [←mul_assoc, ←add_mul, mul_comm r, g, one_mul]
  rw [this]
  apply mem_add
  apply mem_mul_right
  assumption
  apply mem_mul_left
  assumption

end Ideal

namespace Submonoid

variable [RingOps R] [IsRing R] [IsCommMagma R]

def ofMaximalIdeal (i: Ideal R) (hi: i.isMaximal) : Submonoid R :=
  have : ∃s: Submonoid R, s.carrier = i.carrierᶜ  := by
    rw [←Ideal.prime_iff_compl_submonoid]
    apply And.intro
    exact Ideal.prime_of_maximal i hi
    apply lt_of_le_of_ne
    apply le_top
    exact hi.left
  {
    carrier := i.carrierᶜ
    mem_one := by
      obtain ⟨s, h⟩ := this
      show 1 ∈ i.carrierᶜ
      rw [←h]; apply mem_one s
    mem_mul {a b} ha hb := by
      obtain ⟨s, h⟩ := this
      show a * b ∈ i.carrierᶜ
      rw [←h]; rw [←h] at ha hb
      apply mem_mul s
      assumption
      assumption
  }

end Submonoid
