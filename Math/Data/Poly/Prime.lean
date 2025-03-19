import Math.Algebra.Ring.Theory.Ideal.TwoSided.Prime
import Math.Algebra.Ring.Theory.Ideal.TwoSided.Principal
import Math.Data.Poly.Dvd

namespace Poly

variable [RingOps P] [IsRing P] [IsCommMagma P] [NoZeroDivisors P] [IsNontrivial P]

def is_prime_ideal [DecidableEq P]
  (p: P[X])
  [inv: IsInvertible p.lead]
  (spec: ∀a b: P[X],
    a.degree ≠ ⊥ ->
    b.degree ≠ ⊥ ->
    a.degree < p.degree ->
    b.degree < p.degree ->
    a.degree ≤ b.degree ->
    p ∣ a * b -> p ∣ a ∨ p ∣ b) : (Ideal.of_dvd p).IsPrime := by
  intro a b h
  replace h : p ∣ a * b := h
  show p ∣ a ∨ p ∣ b
  unfold char at *
  generalize deg_spec: Poly.degree_add a.degree b.degree = deg
  cases hdeg:deg with
  | bot =>
    have : (a * b).degree = deg := by rw [←deg_spec, Poly.mul_degree]
    rw [hdeg] at this
    rcases of_mul_eq_zero (Poly.degree_eq_bot_iff_eq_zero.mp this) with rfl | rfl
    left; apply dvd_zero
    right; apply dvd_zero
  | of deg =>
    subst hdeg
    induction deg using Nat.strongRecOn generalizing a b with
    | ind deg ih =>
    replace h := h
    rw [Poly.dvd_mod (inv := inv), Poly.mul_mod, ←Poly.dvd_mod] at h
    cases hdeg:degree_add (a.mod p).degree (b.mod p).degree with
    | bot =>
      rw [←mul_degree] at hdeg
      replace h := degree_eq_bot_iff_eq_zero.mp hdeg
      rcases of_mul_eq_zero h with h | h
      left; rwa [mod_eq_zero_iff_dvd]
      right; rwa [mod_eq_zero_iff_dvd]
    | of deg' =>
      rcases a.degree_eq_degreeNat' with ha | ha
      rw [degree_eq_bot_iff_eq_zero.mp ha]
      left; apply dvd_zero
      rcases b.degree_eq_degreeNat' with hb | hb
      rw [degree_eq_bot_iff_eq_zero.mp hb]
      right; apply dvd_zero
      by_cases hx:a.degree < p.degree ∧ b.degree < p.degree
      · cases le_total a.degree b.degree
        apply spec
        rw [ha]; intro; contradiction
        rw [hb]; intro; contradiction
        exact hx.left
        exact hx.right
        assumption
        rwa [mod_of_lt _ _ hx.left, mod_of_lt _ _ hx.right] at h
        rw [Or.comm]
        apply spec
        rw [hb]; intro; contradiction
        rw [ha]; intro; contradiction
        exact hx.right
        exact hx.left
        assumption
        rwa [mod_of_lt _ _ hx.left, mod_of_lt _ _ hx.right, mul_comm] at h
      have := ih _ ?_ _ _ h hdeg
      rw [dvd_mod, dvd_mod b]
      assumption
      suffices WithBot.of deg' < WithBot.of deg by
        cases this; assumption
      rw [←hdeg, ←deg_spec]
      clear hdeg deg_spec
      rw [ha, hb]
      rw [degree_add]
      rw [Decidable.not_and_iff_not_or_not, not_lt, not_lt] at hx
      rcases (b.mod p).degree_eq_degreeNat' with hy | hy
      erw [degree_eq_bot_iff_eq_zero.mp hy, degree_add_bot_right]
      apply WithBot.LT.bot
      rcases (a.mod p).degree_eq_degreeNat' with hz | hz
      erw [degree_eq_bot_iff_eq_zero.mp hz, degree_add_bot_left]
      apply WithBot.LT.bot
      rw [hy, hz, degree_add]
      rcases hx with g | g
      apply WithBot.LT.of
      apply Nat.add_lt_add_of_lt_of_le
      apply WithBot.of_lt.mp
      rw [←hz, ←ha]
      apply lt_of_lt_of_le _ g
      apply mod_degree_lt
      apply WithBot.of_le.mp
      rw [←hy, ←hb]
      apply mod_degree_le_self

      apply WithBot.LT.of
      apply Nat.add_lt_add_of_le_of_lt
      apply WithBot.of_le.mp
      rw [←hz, ←ha]
      apply mod_degree_le_self
      apply WithBot.of_lt.mp
      rw [←hy, ←hb]
      apply lt_of_lt_of_le _ g
      apply mod_degree_lt

end Poly
