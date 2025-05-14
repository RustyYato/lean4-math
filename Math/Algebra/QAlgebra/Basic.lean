import Math.Algebra.Algebra.Defs
import Math.Algebra.QAlgebra.Defs
import Math.Algebra.Field.Hom
import Math.Algebra.AddGroupWithOne.Hom

section

variable [QAlgebraOps α] [IsQAlgebra α]

instance : AlgebraMap ℚ α where
  toFun q := q
  map_zero := by
    rw [ratCast_eq_ratCastRec]
    show _ /? _ ~(_) = _
    rw [div?_eq_mul_inv?]
    simp
  map_one := by
    rw [ratCast_eq_ratCastRec]
    show _ /? _ ~(_) = _
    rw [div?_eq_mul_inv?]
    simp
  map_add := by
    have := (inferInstanceAs (IsQAlgebra α)).toHasChar
    intro a b
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
  map_mul := by
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

def ratCast_inj : Function.Injective (fun a: ℚ => (a: α)) := by
  show Function.Injective algebraMap
  apply field_hom_inj

-- we don't use Semiring here to prevent invert_tactic cycles
-- by using Ring we ensure that Nat is not a valid option
def ratCast_ne_zero (n: ℚ) : n ≠ 0 -> (n: α) ≠ 0 := by
  intro h g
  rw [←ratCast_zero] at g
  have := ratCast_inj g
  contradiction

local macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply ratCast_ne_zero <;> invert_tactic)

@[norm_cast]
def ratCast_mul (a b: ℚ) : a * b = ((a * b: ℚ): α) := by
  symm
  simp only [ratCast_eq_ratCastRec]
  cases a, b with | mk a b =>
  simp
  show ((a.num * b.num: ℤ): α) /? (a.den * b.den: ℕ) ~(_) =
    ((a.num: α) /? a.den ~(_)) * ((b.num: α) /? b.den ~(_))
  simp only [div?_eq_mul_inv?]
  rw [←intCast_mul]
  apply of_mul_right_nonzero _ _ (a.den * b.den: α)
  rw [←natCast_mul]
  intro h; rw [←natCast_zero] at h
  have := HasChar.natCast_inj h
  revert this
  have := a.den_nz
  have := b.den_nz
  show a.den * b.den ≠ 0
  invert_tactic
  rw (occs := [1]) [←natCast_mul]
  rw [mul_assoc, inv?_mul_cancel, mul_one, mul_assoc (a.num: α),
    mul_left_comm _ (b.num: α), mul_assoc, mul_assoc,
    mul_assoc, mul_left_comm _ (a.den: α),
    inv?_mul_cancel, mul_one, inv?_mul_cancel, mul_one]

@[norm_cast]
def ratCast_neg (a: ℚ) : -a = ((-a: ℚ): α) := by
  rw [←neg_one_mul a, ←neg_one_mul (a: α), ←ratCast_mul]
  rw [←intCast_one (α := ℚ), intCast_neg, ratCast_intCast,
    ←intCast_neg, intCast_one]

@[norm_cast]
def ratCast_inv? (a: ℚ) (h: a ≠ 0) : (a: α)⁻¹? = a⁻¹? := by
  apply inv?_eq_of_mul_left
  rw [ratCast_mul, mul_inv?_cancel, ratCast_one]

@[norm_cast]
def ratCast_div? (a b: ℚ) (h: b ≠ 0) : (a: α) /? (b: α) = ((a /? b: ℚ): α) := by
  rw [div?_eq_mul_inv?, div?_eq_mul_inv?, ratCast_inv?, ratCast_mul]

def map_ratCast
  [FunLike F α β]
  [QAlgebraOps α] [QAlgebraOps β]
  [IsZeroHom F α β] [IsOneHom F α β] [IsAddHom F α β] [IsMulHom F α β]
  [IsQAlgebra α] [IsQAlgebra β]
  (f: F) (n: ℚ) : f n = n := by
  rw [ratCast_eq_ratCastRec, ratCast_eq_ratCastRec]
  induction n using Rat.ind with | mk n =>
  show f (_ /? _ ~(_)) = _ /? _ ~(_)
  rw [map_div?]
  congr
  rw [map_intCast]
  rw [map_natCast]

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
    | zero => simp [natCast_zero, map_zero]
    | succ m ih =>
      simp [natCast_succ, map_add, map_one, ih]
  rw [h, ←map_zero (algebraMap (R := ℚ) (α := α))] at this
  replace this := field_hom_inj (F := ℚ) (R := α) algebraMap this
  rw [natCast_inj this]
  apply Nat.dvd_refl

def Rat.cast.inj [QAlgebraOps α] [IsQAlgebra α] : Function.Injective (Rat.cast (α := α)) :=
  field_hom_inj algebraMap

def Rat.castHom [QAlgebraOps α] [IsQAlgebra α] : ℚ ↪+* α := {
  algebraMap with
  inj' := Rat.cast.inj
}


namespace IsQAlgebra.ofAlgebra

variable [FieldOps α] [IsField α] [SMul ℚ α] [AlgebraMap ℚ α] [IsAlgebra ℚ α]

scoped instance : RatCast α where
  ratCast := algebraMap

scoped instance : HasChar α 0 := HasChar.of_ring_emb {
  algebraMap (R := ℚ) with
  inj' := field_hom_inj algebraMap
}

scoped instance : IsQAlgebra α where
  ratCast_eq_ratCastRec := by
    intro q
    induction q using Rat.ind with | mk q =>
    show algebraMap (Rat.mk q) = (q.num: α) /? q.den ~(_)
    have : (q.den: ℚ) ≠ 0 := by
      intro h
      exact q.den_nz (HasChar.natCast_inj h)
    have : Rat.mk q = (q.num: ℚ) /? q.den := by apply ratCast_eq_ratCastRec
    rw [this]
    rw [map_div?]
    congr
    rw [map_intCast]
    rw [map_natCast]
  qsmul_eq_ratCast_mul q a := smul_def _ _

end ofAlgebra

section

variable (A B C: Type*) [QAlgebraOps A] [IsQAlgebra A] [QAlgebraOps B] [IsQAlgebra B]
   [AlgebraMap A B] [SMul A B]
   [IsAlgebra A B] [IsQAlgebra A] [IsQAlgebra B]

instance : IsAlgebraTower ℚ A B where
  algebraMap_algebraMap n := by
    show algebraMap (algebraMap (Rat.cast n: ℚ)) = algebraMap (Rat.cast n: ℚ)
    simp only [map_ratCast]

end
