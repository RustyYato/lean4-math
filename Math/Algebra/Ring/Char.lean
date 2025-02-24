import Math.Algebra.Ring.Defs
import Math.Algebra.Semiring.Char

def HasChar.intCast_inj [RingOps α] [IsRing α] [HasChar α 0]: Function.Injective (fun n: ℤ => (n: α)) := by
  intro n m h
  dsimp at h
  cases n using Int.coe_cases <;>
  cases m using Int.coe_cases <;>
  rename_i n m
  any_goals repeat rw [intCast_ofNat] at h
  any_goals repeat rw [intCast_negSucc] at h
  · congr; apply natCast_inj (α := α); assumption
  · replace h := add_eq_zero_of_eq_neg h
    rw [←natCast_add] at h
    have := HasChar.char_dvd_natCast_eq_zero _ h
    rw [Nat.add_succ] at this
    have := Nat.zero_dvd.mp this
    contradiction
  · replace h := add_eq_zero_of_eq_neg h.symm
    rw [←natCast_add] at h
    have := HasChar.char_dvd_natCast_eq_zero _ h
    rw [Nat.add_succ] at this
    have := Nat.zero_dvd.mp this
    contradiction
  · replace h := neg_inj.mp h
    rw [Nat.succ.inj (natCast_inj h)]
