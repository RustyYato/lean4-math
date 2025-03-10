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

def add_div_add₀ (a b c: α) (hc: c ≠ 0) : a /? c + b /? c = (a + b) /? c := by
  simp [div?_eq_mul_inv?]
  rw [add_mul]

end

section

variable [FieldOps α] [IsField α]

def inv_sub_inv (a b: α) (ha: a ≠ 0) (hb: b ≠ 0) : a⁻¹? - b⁻¹? = (b - a) /? (a * b) := by
  rw [div?_eq_mul_inv?]
  apply of_mul_left_nonzero _ _ (a * b)
  invert_tactic
  rw [mul_sub, mul_assoc, ←div?_eq_mul_inv?, mul_div?_cancel, mul_assoc, mul_inv?_cancel, mul_one]
  rw [mul_comm, mul_assoc, inv?_mul_cancel, mul_one]

def midpoint (a b: α) [NeZero (2: α)] : α := (a + b) /? 2

def midpoint_comm (a b: α) [NeZero (2: α)] : midpoint a b = midpoint b a := by
  unfold midpoint
  rw [add_comm]

def mul_div?_mul (a b c d: α) (hb: b ≠ 0) (hd: d ≠ 0) : (a /? b) * (c /? d) = (a * c) /? (b * d) := by
  simp [div?_eq_mul_inv?]
  rw [inv?_mul_rev]; ac_rfl

end
