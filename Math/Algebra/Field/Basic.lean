import Math.Algebra.Field.Defs
import Math.Algebra.GroupWithZero.Basic

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
  rw [←neg_mul_right, ←neg_mul_left, neg_neg, inv?_mul_cancel]

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
