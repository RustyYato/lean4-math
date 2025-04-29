import Math.Data.Nat.Gcd
import Math.Data.Int.Basic

namespace Int

def gcdA (a b: ℤ) := a.sign * Nat.gcdA a.natAbs b.natAbs
def gcdB (a b: ℤ) := b.sign * Nat.gcdB a.natAbs b.natAbs

def gcd_eq_gcd_ab (x y: ℤ) : gcd x y = x * gcdA x y + y * gcdB x y := by
  have ofnat_mul_sign (x: ℕ) : (x: ℤ) * Int.sign x = x := by
    cases x
    rfl
    simp
  cases x with
  | ofNat x =>
    cases y with
    | ofNat y =>
      simp [gcd, gcdA, gcdB]
      rw [←Int.mul_assoc, ofnat_mul_sign,
        ←Int.mul_assoc, ofnat_mul_sign,
        ←Nat.gcd_eq_gcd_ab]
    | negSucc y =>
      simp [gcd, gcdA, gcdB]
      rw [←Int.mul_assoc, ofnat_mul_sign]
      rw [Int.mul_neg, ←Int.neg_mul, Int.neg_negSucc,
        ←Nat.gcd_eq_gcd_ab]
  | negSucc x =>
    cases y with
    | ofNat y =>
      simp [gcd, gcdA, gcdB]
      rw [←Int.mul_assoc, ofnat_mul_sign,
        Int.mul_neg, ←Int.neg_mul, Int.neg_negSucc,
        ←Nat.gcd_eq_gcd_ab]
    | negSucc y =>
      simp [gcd, gcdA, gcdB]
      rw [
        Int.mul_neg, ←Int.neg_mul, Int.neg_negSucc,
        Int.mul_neg, ←Int.neg_mul, Int.neg_negSucc,
        ←Nat.gcd_eq_gcd_ab]

def gcd_eq_dvd_lincomb (a b: ℤ) : ∀x y, (gcd a b: ℤ) ∣ a * x + b * y := by
  intro x y
  obtain ⟨a₀, aeq⟩ := Int.gcd_dvd_left (a := a) (b := b)
  obtain ⟨b₀, beq⟩ := Int.gcd_dvd_right (a := a) (b := b)
  rw (occs := [2]) [beq, aeq]
  rw [Int.mul_assoc, Int.mul_assoc, ←Int.mul_add]
  apply Int.dvd_mul_right

end Int
