import Math.Algebra.Field.Defs
import Math.Algebra.GroupWithZero.Basic
import Math.Algebra.Group.Hom

section

variable [FieldOps F] [IsNonCommField F] [RingOps R] [IsRing R] [IsNontrivial R]
variable [FunLike α F R] [IsZeroHom α F R] [IsOneHom α F R] [IsAddHom α F R] [IsMulHom α F R]

instance : IsEmbeddingLike α F R where
  coe_inj f := by
    suffices ∀x, f x = 0 -> x = 0 by
      intro x y eq
      have  eq' : f x - f y = 0 := by rw [eq, sub_self]
      rw [←resp_sub] at eq'
      exact eq_of_sub_eq_zero (this _ eq')
    intro x fx
    apply Classical.byContradiction
    intro h
    have : f x * f (x⁻¹?) = 0 := by rw [fx, zero_mul]
    rw [←resp_mul, mul_inv?_cancel, resp_one] at this
    exact zero_ne_one _ this.symm

def field_hom_inj (f: F →+* R) : Function.Injective f :=
  IsEmbeddingLike.coe_inj f

def resp_ne_zero (f: α) : x ≠ 0 -> f x ≠ 0 :=
  fun g h => g (IsEmbeddingLike.coe_inj f (h.trans (resp_zero f).symm))

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply resp_ne_zero <;> invert_tactic)

def resp_ne_zero' (f: α) (n: ℤ) : x ≠ 0 ∨ 0 ≤ n -> f x ≠ 0 ∨ 0 ≤ n := by
  intro h
  cases h
  left
  invert_tactic
  right; assumption

macro_rules
| `(tactic|int_pow_tactic_trivial) => `(tactic|apply resp_ne_zero' <;> int_pow_tactic)

end

section

variable [FieldOps α] [FieldOps β] [IsNonCommField α] [IsNonCommField β]
variable [FunLike F α β] [IsZeroHom F α β] [IsOneHom F α β] [IsAddHom F α β] [IsMulHom F α β]

def resp_inv? (f: F) (a: α) (h: a ≠ 0) : f a⁻¹? = (f a)⁻¹? := by
  refine inv?_eq_of_mul_right (f a) (f a⁻¹?) ?_
  rw [←resp_mul, inv?_mul_cancel, resp_one]

def resp_div? (f: F) (a b: α) (h: b ≠ 0) : f (a /? b) = f a /? f b := by
  rw [div?_eq_mul_inv?, div?_eq_mul_inv?, resp_mul, resp_inv?]

def resp_zpow? (f: F) (a: α) (n: ℤ) (h: a ≠ 0 ∨ 0 ≤ n) : f (a ^? n) = (f a) ^? n := by
  cases n using Int.coe_cases with
  | ofNat n => rw [zpow?_ofNat, zpow?_ofNat, resp_npow]
  | negSucc n =>
    rw [zpow?_negSucc, zpow?_negSucc, resp_npow, resp_inv?]
    apply h.resolve_right
    intro; contradiction

end
