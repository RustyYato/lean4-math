import Math.Data.Poly.Defs
import Math.Algebra.Dvd

namespace Poly

variable [SemiringOps P] [IsSemiring P]

instance : Dvd P[X] where
  dvd a b := ∃k, b = a * k

instance : IsLawfulDvd P[X] where

def divmod (a b: ℤ[X]) (h: IsInvertible (b.toFinsupp b.degree)) : ℤ[X] × ℤ[X] :=
  if a.degree >= b.degree && a.degree > 0 then
    let x := (a.coeffs a.degree) * ⅟(b.coeffs b.degree)
    let z := a - x • b * X^(a.degree - b.degree)
    let (d, m) := divmod z b h
    (d + C x * X ^ (a.degree - b.degree), m)
  else if a.degree = b.degree then
    (C (a.coeffs 0 / b.coeffs 0), C (a.coeffs 0 % b.coeffs 0))
  else
    (0, a)
termination_by a.degree
decreasing_by
  rename_i h₀
  simp at h₀
  apply lt_of_le_of_ne
  · apply degree_is_minimal
    intro i hi
    rw [sub_eq_add_neg, coeffs_add, Pi.apply_add, degree.DegreeLe _ _ hi,
      zero_add]
    rw [smul_def, mul_assoc, ←smul_def]
    simp
    rcases lt_or_le i (a.degree - b.degree) with h₁ | h₁
    rw [coeffs_lt_mul_X_npow, mul_zero]
    assumption
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h₁
    rw [add_comm, coeffs_ge_mul_X_npow, degree.DegreeLe b k, mul_zero]
    omega
  · suffices Poly.DegreeLe z.coeffs (a.degree-1) by
      intro g
      have := degree_is_minimal z _ this
      rw [g] at this
      exact lt_irrefl ((Nat.le_pred_iff_lt h₀.right).mp this)
    intro i hi
    replace hi := Nat.succ_le.mpr hi
    rw [←Nat.pred_eq_sub_one, Nat.succ_pred] at hi
    rcases lt_or_eq_of_le hi with hi | hi
    · unfold z
      rw [smul_def, mul_assoc, ←smul_def]
      simp
      rw [degree.DegreeLe a]
      simp
      rcases lt_or_le i (a.degree - b.degree) with h₁ | h₁
      rw [coeffs_lt_mul_X_npow, mul_zero]
      assumption
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h₁
      rw [add_comm, coeffs_ge_mul_X_npow, degree.DegreeLe b k, mul_zero]
      omega
      assumption
    · unfold z
      subst i
      rw [smul_def, mul_assoc, ←smul_def]
      simp
      conv => {
        lhs; rhs; rhs; rhs
        rw [←Nat.sub_add_cancel h₀.left] }
      rw [add_comm, coeffs_ge_mul_X_npow]
      unfold x
      rw [mul_assoc, invOf, IsInvertible.invOf_mul]
      simp
    · sorry

end Poly
