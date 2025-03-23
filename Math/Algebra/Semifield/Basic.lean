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

def add_div?_add₀ (a b c: α) (hc: c ≠ 0) : a /? c + b /? c = (a + b) /? c := by
  simp [div?_eq_mul_inv?]
  rw [add_mul]

end

section

variable [SemifieldOps α] [IsSemifield α]

def mul_div?_mul (a b c d: α) (hb: b ≠ 0) (hd: d ≠ 0) : (a /? b) * (c /? d) = (a * c) /? (b * d) := by
  simp [div?_eq_mul_inv?]
  rw [inv?_mul_rev]; ac_rfl

end
