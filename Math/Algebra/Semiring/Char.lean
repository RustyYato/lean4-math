import Math.Algebra.Monoid.Char
import Math.Algebra.Semiring.Defs

def char_eq_of_natCast_eq_zero [SemiringOps α] [IsSemiring α] (n: Nat) :
  n = (0: α) -> (∀m: Nat, m = (0: α) -> n ∣ m) -> char α = n := by
  intro h g
  apply char_eq_of
  intro x
  rw [←natCast_mul_eq_nsmul, h, zero_mul]
  intro m g'
  apply g
  rw [natCast_eq_nsmul_one]
  apply g'
