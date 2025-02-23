import Math.Algebra.GroupWithZero.SetLike.Defs
import Math.Algebra.GroupWithZero.Defs
import Math.Algebra.Monoid.SetLike.Basic

variable [SetLike S α] [GroupWithZeroOps α] [IsGroupWithZero α] [IsSubgroupWithZero S]

def mem_div? (s: S) (a b: α) (h: b ≠ 0) : a ∈ s -> b ∈ s -> a /? b ∈ s := by
  intro ha hb
  rw [div?_eq_mul_inv?]
  apply mem_mul
  assumption
  apply mem_inv?
  assumption

def mem_zpow? (s: S) (a: α) (n: ℤ) (h: a ≠ 0 ∨ 0 ≤ n) : a ∈ s -> a ^? n ∈ s := by
  intro ha
  cases n using Int.coe_cases
  rw [zpow?_ofNat]; apply mem_npow
  assumption
  rw [zpow?_negSucc]; apply mem_npow
  apply mem_inv?; assumption
  int_pow_tactic
