import Math.Algebra.GroupWithZero.SetLike.Defs
import Math.Algebra.GroupWithZero.Defs
import Math.Algebra.Monoid.SetLike.Basic

variable [SetLike S α] [GroupWithZeroOps α] [IsGroupWithZero α] [IsSubgroupWithZero S]
  (s: S)

def mem_div? (a b: α) (h: b ≠ 0) : a ∈ s -> b ∈ s -> a /? b ∈ s := by
  intro ha hb
  rw [div?_eq_mul_inv?]
  apply mem_mul
  assumption
  apply mem_inv?
  assumption

def mem_zpow? (a: α) (n: ℤ) (h: a ≠ 0 ∨ 0 ≤ n) : a ∈ s -> a ^? n ∈ s := by
  intro ha
  cases n using Int.coe_cases
  rw [zpow?_ofNat]; apply mem_npow
  assumption
  rw [zpow?_negSucc]; apply mem_npow
  apply mem_inv?; assumption
  int_pow_tactic

instance : CheckedInv? s where
  checked_invert a hj :=
    have : a.val ≠ 0 := by
      cases a; rintro rfl
      contradiction
    ⟨a.val⁻¹?, mem_inv? _ this a.property⟩

instance : CheckedDiv? s where
  checked_div a b h :=
    have : b.val ≠ 0 := by
      cases b; rintro rfl
      contradiction
    ⟨a.val /? b.val, mem_div? _ _ _ this a.property b.property⟩

instance : CheckedIntPow? s where
  checked_pow a n h :=
    have : a.val ≠ 0 ∨ 0 ≤ n := by
      cases h; left
      cases a; rintro rfl
      contradiction
      right; assumption
    ⟨a.val ^? n, mem_zpow? _ _ _ this a.property⟩

instance : IsGroupWithZero s where
  exists_ne := by
    refine ⟨0, 1, ?_⟩
    intro h
    exact zero_ne_one α (Subtype.mk.inj h)
  mul_inv?_cancel := by
    intro a h
    apply Subtype.val_inj
    apply mul_inv?_cancel
  div?_eq_mul_inv? := by
    intro _ _ _
    apply Subtype.val_inj
    apply div?_eq_mul_inv?
  zpow?_ofNat := by
    intro _ _
    apply Subtype.val_inj
    apply zpow?_ofNat
  zpow?_negSucc := by
    intro _ _ _
    apply Subtype.val_inj
    apply zpow?_negSucc
