import Math.Algebra.Semifield.Defs
import Math.Algebra.GroupWithZero.Basic
import Math.Algebra.Semiring.Char

def ne_zero_of_char0' [SemifieldOps α] [IsSemifield α] [IsAddCancel α] [HasChar α 0] (n: ℕ) :
  n ≠ 0 -> (n: α) ≠ 0 := by
  intro h g
  rw [←natCast_zero] at g
  exact h (HasChar.natCast_inj g)

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply ne_zero_of_char0' <;> invert_tactic)

section

variable [SemifieldOps α] [IsNonCommSemifield α]

def midpoint (a b: α) [NeZero (2: α)] : α := (a + b) /? 2

def midpoint_comm (a b: α) [NeZero (2: α)] : midpoint a b = midpoint b a := by
  unfold midpoint
  rw [add_comm]

end

section

variable [SemifieldOps α] [IsSemifield α]

def add_div?_add (a b c d: α) (hb: b ≠ 0) (hd: d ≠ 0) : a /? b + c /? d = (d * a + b * c) /? (b * d) := by
  rw [div?_eq_mul_inv?, div?_eq_mul_inv?, div?_eq_mul_inv?,
    inv?_mul_rev, add_mul,
    mul_comm d, mul_assoc a, ←mul_assoc d, mul_inv?_cancel, one_mul,
    mul_comm b, mul_assoc c, mul_left_comm b, mul_inv?_cancel, mul_one]

def mul_div?_mul (a b c d: α) (hb: b ≠ 0) (hd: d ≠ 0) : (a /? b) * (c /? d) = (a * c) /? (b * d) := by
  simp [div?_eq_mul_inv?]
  rw [inv?_mul_rev]; ac_rfl

end
