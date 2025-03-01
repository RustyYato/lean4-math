import Math.Algebra.Monoid.Units.Defs
import Math.Algebra.Impls.Nat
import Math.Algebra.Impls.Int

class IsIntegralDomain (α: Type*) [RingOps α] extends IsRing α, NoZeroDivisors α, IsNontrivial α, IsCommMagma α where
  mk' ::

def IsIntegralDomain.mk (α: Type*) [RingOps α] [IsRing α] [NoZeroDivisors α] [IsNontrivial α] [IsCommMagma α] : IsIntegralDomain α where

instance [RingOps α] [IsRing α] [NoZeroDivisors α] [IsNontrivial α] [IsCommMagma α] : IsIntegralDomain α where

instance (priority := 10000) : IsIntegralDomain Int := inferInstance

def mul_left_cancel₀ [RingOps α] [IsIntegralDomain α] {k a b: α} (hk: k ≠ 0) : k * a = k * b -> a = b := by
  intro h
  have : k * a - k * b = 0 := by rw [h, sub_self]
  rw [←mul_sub] at this
  cases of_mul_eq_zero this
  contradiction
  apply eq_of_sub_eq_zero
  assumption

def mul_right_cancel₀ [RingOps α] [IsIntegralDomain α] {k a b: α} (hk: k ≠ 0) : a * k = b * k -> a = b := by
  rw [mul_comm _ k, mul_comm _ k]
  apply mul_left_cancel₀
  assumption

class IsLawfulDvd (α: Type*) [Dvd α] [Mul α]: Prop where
  dvd_iff {a b: α} : (a ∣ b) ↔  ∃k, b = a * k := by intros; rfl

export IsLawfulDvd (dvd_iff)

instance : IsLawfulDvd Nat where
instance : IsLawfulDvd Int where

section

variable {α: Type*} [Dvd α]

section

variable [MonoidOps α] [IsMonoid α] [IsLawfulDvd α]

def unit_dvd (a b: α) [IsUnit a] : a ∣ b := by
  rw [dvd_iff]
  exists IsUnit.inv a * b
  rw [←mul_assoc, IsUnit.mul_inv, one_mul]

@[refl]
def dvd_refl (a: α) : a ∣ a := dvd_iff.mpr ⟨1, (mul_one _).symm⟩

def of_dvd_unit (a b: α) [IsUnit b] [IsCommMagma α] : a ∣ b -> IsUnit a := by
  rw [dvd_iff]
  intro ⟨a', _⟩
  subst b
  apply IsUnit.mk
  refine ⟨⟨a, a' * IsUnit.inv (a * a'), ?_, ?_⟩, rfl⟩
  rw [←mul_assoc, IsUnit.mul_inv]
  rw [mul_comm a', mul_assoc, mul_comm a', IsUnit.inv_mul]

structure IsIrreducible (x: α) : Prop where
  notUnit: ¬IsUnit x
  unit_of_prod: ∀a b, x = a * b -> IsUnit a ∨ IsUnit b

structure IsPrime [Zero α] (x: α) : Prop where
  ne_zero: x ≠ 0
  notUnit: ¬IsUnit x
  of_dvd_prod: ∀a b, x ∣ a * b -> x ∣ a ∨ x ∣ b

end

def dvd_mul_left [Mul α] [IsLawfulDvd α] (a b: α) : a ∣ a * b := by
  rw [dvd_iff]
  exists b

def dvd_mul_right [Mul α] [IsCommMagma α] [IsLawfulDvd α] (a b: α) : a ∣ b * a := by
  rw [mul_comm]
  apply dvd_mul_left

def dvd_add {k a b: α} [Mul α] [AddMonoidOps α] [IsNonUnitalNonAssocSemiring α] [IsLawfulDvd α] : k ∣ a -> k ∣ b -> k ∣ a + b := by
  rw [dvd_iff, dvd_iff]
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩
  rw [←mul_add]
  apply dvd_mul_left

def dvd_trans {a b c: α} [Mul α] [IsSemigroup α] [IsLawfulDvd α] : a ∣ b -> b ∣ c -> a ∣ c := by
  rw [dvd_iff, dvd_iff, dvd_iff]
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩
  exists a * b
  rw [mul_assoc]

def dvd_neg [RingOps α] [h: IsRing α] [IsLawfulDvd α] {a b: α} : a ∣ b ↔ a ∣ -b := by
  have := h.toIsSemiring
  rw [dvd_iff, dvd_iff]
  apply Iff.intro
  rintro ⟨k, rfl⟩
  exists -k
  rw [neg_mul_right]
  intro ⟨k, eq⟩
  exists -k
  rw [←neg_mul_right, ←eq, neg_neg]

def dvd_zero [Mul α] [Zero α] [IsMulZeroClass α] [IsLawfulDvd α] (a: α) : a ∣ 0 := by
  rw [dvd_iff]
  exists 0
  rw [mul_zero]

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
