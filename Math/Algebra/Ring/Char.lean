import Math.Algebra.Ring.Defs
import Math.Algebra.Semiring.Char

def HasChar.natCast_inj [RingOps α] [IsRing α] [HasChar α 0]: Function.Injective (fun n: ℕ => (n: α)) := by
  suffices ∀n m: ℕ, (n: α) = m -> n ≤ m -> n = m by
    intro n m eq
    rcases Nat.le_total n m with h | h
    apply this
    assumption
    assumption
    symm; apply this
    symm; assumption
    assumption
  intro n m eq h
  have : ((m - n: ℕ): α) + n = 0 + m := by
    rw [←intCast_ofNat, ←intCast_ofNat n, ←intCast_ofNat m]
    rw [Int.ofNat_sub h, intCast_sub, sub_add_cancel, zero_add]
  rw [eq] at this
  have := add_right_cancel this
  have := HasChar.char_dvd_natCast_eq_zero _ this
  have := Nat.zero_dvd.mp this
  have := Nat.le_of_sub_eq_zero this
  apply Nat.le_antisymm <;> assumption

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
