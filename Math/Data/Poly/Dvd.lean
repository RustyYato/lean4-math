import Math.Data.Poly.Degree
import Math.Algebra.Dvd
import Math.Order.TopBot.Linear

def Nat.sub_sub' (a b c: Nat) (h: c ≤ b) : a - (b - c) = a + c - b := by omega

namespace Poly

variable [SemiringOps P] [IsSemiring P]

instance : Dvd P[X] where
  dvd a b := ∃k, b = a * k

instance : IsLawfulDvd P[X] where

end Poly

namespace Poly

variable [RingOps P] [IsRing P] [IsCommMagma P] [DecidableEq P] [IsNontrivial P] [IsCommMagma P]

def divmod [IsNontrivial P] [IsCommMagma P] (a b: P[X]) (h: IsInvertible (b.toFinsupp b.degreeNat)) : P[X] × P[X] :=
  if a.degree >= b.degree then
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
  have bdeg_nontrivial : ⊥ < b.degree := by
    unfold degreeNat at h
    split at h
    rename_i h'
    rw [h']
    apply WithBot.LT.bot
    rename_i h'
    cases degree_eq_bot_iff_eq_zero.mp h'
    have : ∀x, AddMonoidAlgebra.toFinsupp (0: P[X]) x = 0 := fun _ => rfl
    rw [this] at h
    have := h.invOf_mul
    rw [mul_zero] at this
    have := zero_ne_one _ this
    contradiction
  have adeg_nontrivial : ⊥ < a.degree := by
    apply lt_of_lt_of_le bdeg_nontrivial
    assumption
  cases hd:a.degree with
  | bot =>
    rw [hd] at adeg_nontrivial
    contradiction
  | of deg =>
    have bdeg_eq_degNat : b.degree = b.degreeNat := by
      unfold degreeNat
      split; assumption
      rename_i g
      replace g : b.degree = ⊥ := g
      cases degree_eq_bot_iff_eq_zero.mp g
      have : ∀x, AddMonoidAlgebra.toFinsupp (0: P[X]) x = 0 := fun _ => rfl
      rw [this] at h
      have := h.invOf_mul
      rw [mul_zero] at this
      contradiction
    have adegnat : a.degreeNat = deg := by
      rw [degree_eq_degreeNat] at hd
      cases hd; rfl
      exact adeg_nontrivial
    apply degree_lt
    intro i hi
    rw [bdeg_eq_degNat, a.degree_eq_degreeNat adeg_nontrivial] at h₀
    cases h₀; rename_i h₁
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

def divmod_of_lt (a b: P[X]) {inv: IsInvertible (b.toFinsupp b.degreeNat)} (h: a.degree < b.degree) : a.divmod b inv = (0, a) := by
  unfold divmod
  rw [if_neg]
  apply not_le_of_lt
  assumption
def divmod_of_le (a b: P[X]) {inv: IsInvertible (b.toFinsupp b.degreeNat)} (h: b.degree ≤ a.degree) :
  a.divmod b inv =
    let x := (a.toFinsupp a.degreeNat) * ⅟(b.toFinsupp b.degreeNat)
    let z := a - x • b * X^(a.degreeNat - b.degreeNat)
    let (d, m) := divmod z b inv
    (d + C x * X ^ (a.degreeNat - b.degreeNat), m) := by
    rw [divmod]
    rw [if_pos h]


end Poly
