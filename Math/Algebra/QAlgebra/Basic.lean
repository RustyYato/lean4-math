import Math.Algebra.Basic
import Math.Algebra.QAlgebra.Defs
import Math.Algebra.Field.Basic

variable [QAlgebraOps α] [IsQAlgebra α]

instance : AlgebraMap ℚ α where
  toFun q := q
  resp_zero := by
    dsimp
    rw [ratCast_eq_ratCastRec]
    show _ /? _ ~(_) = _
    rw [div?_eq_mul_inv?]
    simp [intCast_zero]
  resp_one := by
    dsimp
    rw [ratCast_eq_ratCastRec]
    show _ /? _ ~(_) = _
    rw [div?_eq_mul_inv?]
    simp [intCast_one]
    apply inv?_eq_of_mul_left
    simp [natCast_one]
  resp_add := by
    intro a b
    simp
    cases a, b with | mk a b =>
    simp
    simp [ratCast_eq_ratCastRec]
    show _ /? _ ~(_) = _ /? _ ~(_) + _ /? _ ~(_)
    simp
    rw [
      ←mul_one ((a.num: α) /? (a.den: α) ~(_)),
      ←one_mul ((b.num: α) /? (b.den: α) ~(_))]
    rw (occs := [1]) [←div?_self (α := α) b.den]
    rw (occs := [1]) [←div?_self (α := α) a.den]
    rw [mul_div?_mul, mul_div?_mul, add_div_add₀]
    congr
    rw (occs := [2]) [←intCast_ofNat a.den]
    rw (occs := [2]) [←intCast_ofNat b.den]
    rw [←intCast_mul, ←intCast_mul, ←intCast_add]
    ac_rfl
    rw [natCast_mul]
    intro h
    rw [←natCast_zero] at h
    exact a.den_nz (HasChar.natCast_inj h)
    intro h
    rw [←natCast_zero] at h
    exact b.den_nz (HasChar.natCast_inj h)
  resp_mul := by
    intro a b
    cases a, b with | mk a b =>
    simp [ratCast_eq_ratCastRec]
    show (_ /? _ ~(_)) = (_ /? _ ~(_)) * (_ /? _ ~(_))
    simp
    rw [mul_div?_mul]
    congr
    rw [intCast_mul]
    rw [natCast_mul]

instance : IsAlgebra ℚ α where
  commutes := by
    intro a b
    rw [mul_comm]
  smul_def _ _ := by
    rw [qsmul_eq_ratCast_mul]
    rfl
