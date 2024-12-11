namespace Nat

def dvd_left_of_dvd_of_gcd_eq_one (a b c: Nat) : a ∣ b * c -> a.gcd c = 1 -> a ∣ b := by
  intro dvd gcd_eq
  have p1 := Nat.gcd_mul_dvd_mul_gcd a b c
  rw [gcd_eq, Nat.mul_one] at p1
  have p2 : a.gcd b ∣ a.gcd (b * c) := gcd_dvd_gcd_mul_right_right a b c
  have := Nat.dvd_antisymm p1 p2
  refine gcd_eq_left_iff_dvd.mpr ?_
  rw [←this]
  refine gcd_eq_left_iff_dvd.mp ?_
  assumption

end Nat
