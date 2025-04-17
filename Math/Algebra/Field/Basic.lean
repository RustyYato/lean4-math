import Math.Algebra.Field.Defs
import Math.Algebra.Semifield.Basic
import Math.Algebra.Ring.Basic

section

variable [FieldOps α] [IsNonCommField α]

def neg_ne_zero_of_ne_zero {a: α} (h: a ≠ 0) : -a ≠ 0 := by
  rw [←neg_zero]
  intro h
  rw [neg_inj] at h
  contradiction

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply neg_ne_zero_of_ne_zero <;> invert_tactic)

def neg_inv? (a: α) (h: a ≠ 0) : (-a)⁻¹? = -a⁻¹? := by
  symm
  refine inv?_eq_of_mul_right (-a) (-a⁻¹?) ?_
  rw [mul_neg, neg_mul, neg_neg, inv?_mul_cancel]

def sub_div?_sub₀ (a b c: α) (hc: c ≠ 0) : a /? c - b /? c = (a - b) /? c := by
  simp [div?_eq_mul_inv?]
  rw [sub_mul]

def sub_half [NeZero (2: α)] (a: α) : a - a /? 2 = a /? 2 := by
  rw (occs := [1]) [←div?_mul_cancel a 2]
  rw [mul_two, add_sub_cancel']

end

section

variable [FieldOps α] [IsField α]

def inv_sub_inv (a b: α) (ha: a ≠ 0) (hb: b ≠ 0) : a⁻¹? - b⁻¹? = (b - a) /? (a * b) := by
  rw [div?_eq_mul_inv?]
  apply of_mul_left_nonzero _ _ (a * b)
  invert_tactic
  rw [mul_sub, mul_assoc, ←div?_eq_mul_inv?, mul_div?_cancel, mul_assoc, mul_inv?_cancel, mul_one]
  rw [mul_comm, mul_assoc, inv?_mul_cancel, mul_one]

end

-- we don't use Semiring here to prevent invert_tactic cycles
-- by using Ring we ensure that Nat is not a valid option
def ne_zero_of_char0 [RingOps α] [IsRing α] [HasChar α 0] (n: ℕ) :
  n ≠ 0 -> (n: α) ≠ 0 := by
  intro h g
  rw [←natCast_zero] at g
  exact h (HasChar.natCast_inj g)

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply ne_zero_of_char0 <;> invert_tactic)
