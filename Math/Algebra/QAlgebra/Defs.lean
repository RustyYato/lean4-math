import Math.Algebra.Monoid.Char
import Math.Algebra.Field.Defs
import Math.Data.Rat.Basic

class RatCast (α: Type*) where
  ratCast: ℚ -> α

def Rat.cast [RatCast α] (a: ℚ) : α := RatCast.ratCast a

instance [RatCast α] : Coe ℚ α where
  coe := Rat.cast

attribute [coe] Rat.cast

def ratCastRec [FieldOps α] [IsField α] [HasChar α 0] (q: ℚ) : α :=
  q.lift (fun q => (q.num: α) /? (q.den: α) ~(by
    intro h
    rw [←natCast_zero] at h
    have := HasChar.natCast_inj h
    have := q.den_nz
    contradiction)) (by
      intro a b eq
      dsimp
      let aden := a.den
      apply of_mul_right_nonzero (k := (aden: α))
      · intro h
        rw [←natCast_zero] at h
        exact a.den_nz (HasChar.natCast_inj h)
      rw [div?_mul_cancel]
      let bden := b.den
      apply of_mul_right_nonzero (k := (bden: α))
      · intro h
        rw [←natCast_zero] at h
        exact b.den_nz (HasChar.natCast_inj h)
      rw [mul_comm_right, div?_mul_cancel]
      rw [←intCast_ofNat , ←intCast_ofNat aden, intCast_mul, intCast_mul, eq])


class QAlgebraOps (α: Type*) extends FieldOps α, RatCast α, SMul ℚ α where

instance (priority := 50) [FieldOps α] [RatCast α] [SMul ℚ α] : QAlgebraOps α where

class IsQAlgebra (α: Type*) [QAlgebraOps α] extends IsField α, HasChar α 0 where
  qsmul_eq_ratCast_mul: ∀(q: ℚ) (a: α), q • a = q * a := by intro q a; rfl
  ratCast_eq_ratCastRec: ∀q: ℚ, (q: α) = ratCastRec q

instance : QAlgebraOps ℚ where
  ratCast := id

instance : IsQAlgebra ℚ where
  ratCast_eq_ratCastRec := by
    intro q
    show q = _
    cases q with | mk q =>
    unfold ratCastRec
    show _ = _ /? _ ~(_)
    apply of_mul_right_nonzero (k := (q.den: ℚ))
    intro h
    replace h := HasChar.natCast_inj h
    exact Rat.Fract.den_nz _ h
    rw [div?_mul_cancel]
    apply Quotient.sound
    show _ = _
    simp

variable [QAlgebraOps α] [IsQAlgebra α]

def qsmul_eq_ratCast_mul: ∀(q: ℚ) (a: α), q • a = q * a := IsQAlgebra.qsmul_eq_ratCast_mul
def ratCast_eq_ratCastRec: ∀q: ℚ, (q: α) = @ratCastRec α _ _ IsQAlgebra.toHasChar q := IsQAlgebra.ratCast_eq_ratCastRec

@[norm_cast]
def ratCast_intCast (n: ℤ) : ((n: ℚ): α) = n := by
  rw [ratCast_eq_ratCastRec]
  show ((n: ℤ): α) /? (1:) = _
  rw [div?_eq_mul_inv?]
  conv => { lhs; rhs; arg 1; rw [natCast_one] }
  rw [inv?_one, mul_one]

@[norm_cast]
def ratCast_natCast (n: ℕ) : ((n: ℚ): α) = n := by
  rw [←intCast_ofNat (n := n)]
  rw [ratCast_intCast, intCast_ofNat]

@[norm_cast]
def ratCast_zero : ((0: ℚ): α) = 0 := by
  rw [←natCast_zero, ratCast_natCast, natCast_zero]
@[norm_cast]
def ratCast_one : ((1: ℚ): α) = 1 := by
  rw [←natCast_one, ratCast_natCast, natCast_one]
