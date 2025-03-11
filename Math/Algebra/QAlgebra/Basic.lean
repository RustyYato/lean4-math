import Math.Algebra.Basic
import Math.Algebra.QAlgebra.Defs
import Math.Algebra.Field.Hom

section

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
    rw [mul_div?_mul, mul_div?_mul, add_div?_add₀]
    congr
    rw (occs := [2]) [←intCast_ofNat a.den]
    rw (occs := [2]) [←intCast_ofNat b.den]
    norm_cast
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

end

-- given a non-trivial ring which is an algebra over ℚ, we can show that it must
-- have characteristic 0. This follows pretty much directly from the fact that
-- all ring homomorphisms from fields to non-trivial rings are injective
def HasChar.ofQAlgebra [IsNontrivial α] [RingOps α] [IsRing α] [SMul ℚ α] [AlgebraMap ℚ α] [IsAlgebra ℚ α] : HasChar α 0 := by
  apply HasChar.of_natCast_eq_zero
  rw [natCast_zero]
  intro m h
  have : (algebraMap (m: ℚ): α) = m := by
    clear h
    induction m with
    | zero => simp [natCast_zero, resp_zero]
    | succ m ih =>
      simp [natCast_succ, resp_add, resp_one, ih]
  rw [h, ←resp_zero (algebraMap (R := ℚ) (A := α))] at this
  replace this := field_hom_inj (F := ℚ) (R := α) algebraMap this
  rw [natCast_inj this]
  apply Nat.dvd_refl
