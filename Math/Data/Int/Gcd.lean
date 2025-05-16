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

def dvd_left_of_dvd_of_gcd_eq_one (a b c: ℤ) : a ∣ b * c -> a.gcd c = 1 -> a ∣ b := by
  rw [←Int.natAbs_dvd_natAbs, Int.natAbs_mul, ←Int.natAbs_dvd_natAbs]
  intros
  apply Nat.dvd_left_of_dvd_of_gcd_eq_one
  assumption
  assumption

def mul_dvd (n m: ℤ) (k: ℤ) (h: gcd n m = 1) : n ∣ k -> m ∣ k -> (n * m) ∣ k := by
  intro hn hm
  obtain ⟨q, rfl⟩ := hn
  rw [Int.mul_comm] at hm
  replace hm := dvd_left_of_dvd_of_gcd_eq_one _ _ _ hm (by rwa [gcd_comm])
  obtain ⟨r, rfl⟩ := hm
  rw [←Int.mul_assoc]
  apply Int.dvd_mul_right

def chinese_remainder_unique (x y n m: ℤ) (h: gcd n m = 1) (hn: x % n = y % n) (hm: x % m = y % m) : x % (n * m) = y % (n * m) := by
  refine if gn:n = 0 then ?_ else ?_
  subst n
  simp at *; assumption
  refine if gm:m = 0 then ?_ else ?_
  subst m
  simp at *; assumption
  have : NeZero n := ⟨gn⟩
  have : NeZero m := ⟨gm⟩
  have n_dvd : n ∣ (x - y) := by
    refine dvd_iff_emod_eq_zero.mpr ?_
    rw [Int.sub_emod, hn]
    simp
  have m_dvd : m ∣ (x - y) := by
    refine dvd_iff_emod_eq_zero.mpr ?_
    rw [Int.sub_emod, hm]
    simp
  have nm_dvd_sub := mul_dvd _ _ _ h n_dvd m_dvd
  refine emod_eq_emod_iff_emod_sub_eq_zero.mpr ?_
  exact emod_eq_zero_of_dvd nm_dvd_sub

def chinese_remainder (x y n m: ℤ) : ℤ :=
  y * n * gcdA n m + x * m * gcdB n m

def chinese_remainder_mod_left (x y n m: ℤ) (h: gcd n m = 1) : (chinese_remainder x y n m) % n = x % n := by
  unfold chinese_remainder
  have := Int.gcd_eq_gcd_ab n m
  rw [h] at this
  simp at this
  rw [Int.add_comm, ←Int.sub_eq_iff_eq_add] at this
  rw [Int.mul_assoc _ m, ←this, Int.mul_sub, ←Int.add_sub_assoc,
    Int.add_comm, Int.add_sub_assoc, Int.mul_left_comm, Int.mul_comm _ n, Int.mul_assoc, ←Int.mul_sub]
  rw [Int.add_emod, Int.mul_emod_right, Int.add_zero, Int.mul_one, Int.emod_emod]
def chinese_remainder_mod_right (x y n m: ℤ) (h: gcd n m = 1) : (chinese_remainder x y n m) % m = y % m := by
  unfold chinese_remainder
  have := Int.gcd_eq_gcd_ab n m
  rw [h] at this
  simp at this
  rw [←Int.sub_eq_iff_eq_add] at this
  rw [Int.add_comm, Int.mul_assoc _ n, ←this, Int.mul_sub, ←Int.add_sub_assoc,
    Int.add_comm, Int.add_sub_assoc, Int.mul_left_comm, Int.mul_comm _ m, Int.mul_assoc, ←Int.mul_sub]
  rw [Int.add_emod, Int.mul_emod_right, Int.add_zero, Int.mul_one, Int.emod_emod]

end Int
