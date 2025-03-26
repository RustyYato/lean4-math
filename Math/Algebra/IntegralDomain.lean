import Math.Algebra.Dvd
import Math.Algebra.GroupWithZero.Defs

class IsIntegralDomain (α: Type*) [RingOps α] extends IsRing α, NoZeroDivisors α, IsNontrivial α, IsCommMagma α where
  mk' ::

def IsIntegralDomain.mk (α: Type*) [RingOps α] [IsRing α] [NoZeroDivisors α] [IsNontrivial α] [IsCommMagma α] : IsIntegralDomain α where

instance [RingOps α] [IsRing α] [NoZeroDivisors α] [IsNontrivial α] [IsCommMagma α] : IsIntegralDomain α where

instance (priority := 10000) : IsIntegralDomain Int := inferInstance

instance [RingOps α] [IsIntegralDomain α] : IsLeftCancel₀ α where
  mul_left_cancel₀ := by
    intro a b k hk h
    have : k * a - k * b = 0 := by rw [h, sub_self]
    rw [←mul_sub] at this
    cases of_mul_eq_zero this
    contradiction
    apply eq_of_sub_eq_zero
    assumption
instance [RingOps α] [IsIntegralDomain α] : IsMulCancel₀ α where

section

variable {α: Type*} [Dvd α] [MonoidOps α] [IsMonoid α] [IsLawfulDvd α]

structure IsIrreducible (x: α) : Prop where
  notUnit: ¬IsUnit x
  unit_of_prod: ∀a b, x = a * b -> IsUnit a ∨ IsUnit b

structure IsPrime [Zero α] (x: α) : Prop where
  ne_zero: x ≠ 0
  notUnit: ¬IsUnit x
  of_dvd_prod: ∀a b, x ∣ a * b -> x ∣ a ∨ x ∣ b

end

-- in an integral domain, all prime elements are irreducible
def IsPrime.toIsIrreducible [RingOps α] [IsIntegralDomain α] [Dvd α] [IsLawfulDvd α] {p: α} (h: IsPrime p) : IsIrreducible p where
  notUnit := h.notUnit
  unit_of_prod a b h := by
    subst p
    rcases h.of_dvd_prod a b (by rfl) with h | h
    all_goals rw [dvd_iff] at h
    · obtain ⟨k, eq⟩ := h
      conv at eq => { lhs; rw [←mul_one a] }
      rw [mul_assoc] at eq
      have := mul_left_cancel₀ ?_ eq
      right
      refine ⟨⟨b, k, ?_, ?_⟩, rfl⟩
      rw [←this]
      rw [mul_comm, ←this]
      intro h
      subst h
      rw [zero_mul] at h
      have := h.ne_zero
      contradiction
    · obtain ⟨k, eq⟩ := h
      conv at eq => { lhs; rw [←mul_one b] }
      rw [mul_comm a, mul_assoc] at eq
      have := mul_left_cancel₀ ?_ eq
      left
      refine ⟨⟨a, k, ?_, ?_⟩, rfl⟩
      rw [←this]
      rw [mul_comm, ←this]
      intro h
      subst h
      rw [mul_zero] at h
      have := h.ne_zero
      contradiction

def IsPrime.NatIsIreducible {p: Nat} (h: IsPrime p) : IsIrreducible p where
  notUnit := h.notUnit
  unit_of_prod a b g := by
    subst p
    rcases h.of_dvd_prod a b (by rfl) with h | h
    all_goals rw [dvd_iff] at h
    · obtain ⟨k, eq⟩ := h
      conv at eq => { lhs; rw [←mul_one a] }
      rw [mul_assoc] at eq
      have := Nat.mul_left_cancel ?_ eq
      right
      refine ⟨⟨b, k, ?_, ?_⟩, rfl⟩
      rw [←this]
      rw [mul_comm, ←this]
      apply Nat.zero_lt_of_ne_zero
      intro h
      subst h
      rw [zero_mul] at h
      have := h.ne_zero
      contradiction
    · obtain ⟨k, eq⟩ := h
      conv at eq => { lhs; rw [←mul_one b] }
      rw [mul_comm a, mul_assoc] at eq
      have := Nat.mul_left_cancel ?_ eq
      left
      refine ⟨⟨a, k, ?_, ?_⟩, rfl⟩
      rw [←this]
      rw [mul_comm, ←this]
      apply Nat.zero_lt_of_ne_zero
      intro h
      subst h
      rw [mul_zero] at h
      have := h.ne_zero
      contradiction
