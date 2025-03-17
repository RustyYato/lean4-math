import Math.Data.Poly.Degree
import Math.Algebra.Dvd
import Math.Order.TopBot.Linear

def Nat.sub_sub' (a b c: Nat) (h: c ≤ b) : a - (b - c) = a + c - b := by omega

namespace Poly

variable [SemiringOps P] [IsSemiring P]

instance : Dvd P[X] where
  dvd a b := ∃k, b = a * k

instance : IsLawfulDvd P[X] where

def divmod (a b: ℤ[X]) (h: IsInvertible (b.toFinsupp b.degreeNat)) : ℤ[X] × ℤ[X] :=
  if a.degree >= b.degree && a.degree > ⊥ then
    let x := (a.toFinsupp a.degreeNat) * ⅟(b.toFinsupp b.degreeNat)
    let z := a - x • b * X^(a.degreeNat - b.degreeNat)
    let (d, m) := divmod z b h
    (d + C x * X ^ (a.degreeNat - b.degreeNat), m)
  else
    (0, a)
termination_by a.degree
decreasing_by
  rename_i h₀
  simp at h₀
  show _ < a.degree
  let a' := a - (a.toFinsupp a.degreeNat * ⅟(b.toFinsupp b.degreeNat)) • b * X ^ (a.degreeNat - b.degreeNat)
  show a'.degree < _
  cases hd:a.degree with
  | bot =>
    rw [hd] at h₀
    have := h₀.right
    contradiction
  | of deg =>
    have bdeg_eq_degNat : b.degree = b.degreeNat := by
      unfold degreeNat
      split; assumption
      rename_i g
      replace g : b.degree = ⊥ := g
      cases degree_eq_bot_iff_eq_zero.mp g
      have : ∀x, AddMonoidAlgebra.toFinsupp (0: ℤ[X]) x = 0 := fun _ => rfl
      rw [this] at h
      have := h.invOf_mul
      rw [mul_zero] at this
      contradiction
    have adegnat : a.degreeNat = deg := by
      rw [degree_eq_degreeNat] at hd
      cases hd; rfl
      exact h₀.right
    apply degree_lt
    intro i hi
    have h₁ := h₀.left
    rw [bdeg_eq_degNat, a.degree_eq_degreeNat h₀.right] at h₁
    cases h₁; rename_i h₁
    rcases lt_or_eq_of_le hi with hi | rfl
    · unfold a'
      rw [sub_eq_add_neg]
      show a.toFinsupp i + AddMonoidAlgebra.toFinsupp (-_) i = _
      rw [neg_mul_left, ←neg_smul', coeff_mul_Xpow, Nat.sub_sub', Nat.add_comm i,
        Nat.add_sub_assoc]
      show _ + _ * -(b.toFinsupp (b.degreeNat + (i - a.degreeNat))) = 0
      rw (occs := [2]) [b.of_degree_lt]
      rw [neg_zero, mul_zero]

      rw [a.of_degree_lt _ (hd ▸ (WithBot.LT.of hi)), zero_add]
      rw [bdeg_eq_degNat]
      apply WithBot.LT.of
      simp; omega
      apply le_of_lt
      rw [adegnat]
      assumption
      rw [a.degree_eq_degreeNat h₀.right, bdeg_eq_degNat] at h₀
      cases h₀.left
      assumption
      omega
    · unfold a'
      rw [sub_eq_add_neg]
      show a.toFinsupp deg + AddMonoidAlgebra.toFinsupp (-_) deg = _
      rw [neg_mul_left, ←neg_smul', coeff_mul_Xpow, Nat.sub_sub', Nat.add_comm deg,
        Nat.add_sub_assoc]
      show _ + _ * -(b.toFinsupp (b.degreeNat + (deg - a.degreeNat))) = 0
      rw [adegnat, Nat.sub_self, add_zero, ←neg_mul_right,
        mul_assoc, IsInvertible.invOf_mul, mul_one, add_neg_cancel]
      rw [adegnat]
      · assumption
      · omega

end Poly
