import Math.Algebra.Monoid.Hom
import Math.Algebra.GroupWithZero.Basic

section

variable [GroupWithZeroOps α] [GroupWithZeroOps β] [IsGroupWithZero α] [IsGroupWithZero β]
variable [EmbeddingLike F α β] [IsZeroHom F α β] [IsOneHom F α β] [IsMulHom F α β]

def map_ne_zero (f: F) : x ≠ 0 -> f x ≠ 0 :=
  fun g h => g ((f: α ↪ β).inj (h.trans (map_zero f).symm))

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply map_ne_zero <;> invert_tactic)

def map_ne_zero' (f: F) (n: ℤ) : x ≠ 0 ∨ 0 ≤ n -> f x ≠ 0 ∨ 0 ≤ n := by
  intro h
  cases h
  left
  invert_tactic
  right; assumption

macro_rules
| `(tactic|int_pow_tactic_trivial) => `(tactic|apply map_ne_zero' <;> int_pow_tactic)

def map_inv? (f: F) (a: α) (h: a ≠ 0) : f a⁻¹? = (f a)⁻¹? := by
  refine inv?_eq_of_mul_right (f a) (f a⁻¹?) ?_
  rw [←map_mul, inv?_mul_cancel, map_one]

def map_div? (f: F) (a b: α) (h: b ≠ 0) : f (a /? b) = f a /? f b := by
  rw [div?_eq_mul_inv?, div?_eq_mul_inv?, map_mul, map_inv?]

def map_zpow? (f: F) (a: α) (n: ℤ) (h: a ≠ 0 ∨ 0 ≤ n) : f (a ^? n) = (f a) ^? n := by
  cases n using Int.coe_cases with
  | ofNat n => rw [zpow?_ofNat, zpow?_ofNat, map_npow]
  | negSucc n =>
    rw [zpow?_negSucc, zpow?_negSucc, map_npow, map_inv?]
    apply h.resolve_right
    intro; contradiction

end
