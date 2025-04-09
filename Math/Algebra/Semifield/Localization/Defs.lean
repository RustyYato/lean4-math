-- Use the field of fractions construction to create the localization
-- of a commutative domain

import Math.Algebra.Semiring.Localization.Defs
import Math.Algebra.Semifield.Defs

namespace Localization

variable {R: Type*} [SemiringOps R] [IsSemiring R] [IsCommMagma R] [NoZeroDivisors R]
  [IsNontrivial R]

def Submonoid.Dividends
  (R: Type*) [SemiringOps R] [IsSemiring R] [IsCommMagma R] [NoZeroDivisors R]
  [IsNontrivial R]
   : Submonoid R where
  carrier := Set.mk (· ≠ 0)
  mem_one := (zero_ne_one _).symm
  mem_mul {a b} ha hb h := by cases of_mul_eq_zero h <;> contradiction

private def mem_dividends (r : R) (s : (Submonoid.Dividends R))
  (h : mk (Submonoid.Dividends R) r s ≠ 0): r ∈ Submonoid.Dividends R := by
  rintro rfl
  apply h
  apply zero_eq

instance : CheckedInv? (Localization (Submonoid.Dividends R)) where
  checked_invert a := by
    apply a.hrec _ _ _
    all_goals clear a
    · intro r s  h
      refine mk _ s.val ⟨r, ?_⟩
      apply mem_dividends <;> assumption
    · intro a c b d h
      apply Function.hfunext
      rw [sound _ h]
      intro h₀ h₁ heq
      simp; apply sound
      rw [con_iff_exists] at *
      simp
      obtain ⟨k, eq⟩ := h
      simp at eq; exists k
      symm; rwa [mul_comm c, mul_comm a]

instance : CheckedDiv? (Localization (Submonoid.Dividends R)) where
  checked_div a b h := a * b⁻¹?

instance : CheckedIntPow? (Localization (Submonoid.Dividends R)) :=
  instCheckedIntPow

def mk_inv? (a b) (ha: mk (Submonoid.Dividends R) a b ≠ 0) :
  (mk (Submonoid.Dividends R) a b)⁻¹? = (mk (Submonoid.Dividends R) b.val ⟨a, by
    apply mem_dividends <;> assumption⟩) := rfl

instance : IsGroupWithZero (Localization (Submonoid.Dividends R)) where
  exists_ne := by
    refine ⟨0, 1, ?_⟩
    intro h
    replace h := exact _ h
    rw [con_iff_exists] at h
    obtain ⟨⟨a, ha⟩, h⟩ := h
    simp at h
    exact ha h.symm
  mul_inv?_cancel a h := by
    induction a with | mk a b =>
    obtain ⟨b, hb⟩ := b
    simp [mk_inv?, mk_mul]
    rw [mul_comm]
    apply mk_self _ ⟨b * a, ?_⟩
    apply mem_dividends _ (⟨b, hb⟩ * ⟨b, hb⟩)
    rwa [mk_mul_cancel_left _ a ⟨b, hb⟩ (k := ⟨b, hb⟩)]
  div?_eq_mul_inv? _ _ _ := rfl
  zpow?_ofNat _ _ := rfl
  zpow?_negSucc _ _ _ := rfl

open Classical

instance : IsSemifield (Localization (Submonoid.Dividends R)) where

end Localization
