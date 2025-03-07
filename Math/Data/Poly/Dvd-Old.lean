import Math.Data.Poly.Basic

namespace Poly

def divmod (a b: ℤ[X]) (h: IsInvertible (b.coeffs b.degree)) : ℤ[X] × ℤ[X] :=
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

def x: ℤ[X] := 3*X^4+ 2*X^3+10*X
def y: ℤ[X] := X^2+C 1
def z := (divmod x y ⟨1, by
  rw [y, npow_two]
  simp [x_ne_zero], by
  rw [y, npow_two]
  simp [x_ne_zero]⟩)
-- def z : ℤ[X] × ℤ[X] := (2 * X, 8 * X)



def o: ℤ[X] := y * z.1 + z.2

-- def z₀ := List.ofFn (n := z.1.degree+1) (fun x => z.1.coeffs x.val)

-- #reduce z.fst.degree

-- example : z₀ = [] := by
--   unfold z₀
--   simp only [List.ofFn_succ, List.ofFn_zero]

--   sorry

#eval! List.ofFn (n := x.degree+1) (fun i => x.coeffs i.val)
#eval! List.ofFn (n := o.degree+1) (fun i => o.coeffs i.val)

#eval! List.ofFn (n := z.1.degree+1) (fun i => z.1.coeffs i.val)
#eval! List.ofFn (n := z.2.degree+1) (fun i => z.2.coeffs i.val)

end Poly
