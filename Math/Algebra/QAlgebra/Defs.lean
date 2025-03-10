import Math.Algebra.Monoid.Char
import Math.Algebra.Field.Defs
import Math.Data.Rat.Basic

class RatCast (α: Type*) where
  ratCast: ℚ -> α

instance [RatCast α] : Coe ℚ α where
  coe := RatCast.ratCast

attribute [coe] RatCast.ratCast

def ratCastRec [FieldOps α] [IsField α] (q: ℚ) [HasChar α 0] : α :=
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
      rw [←intCast_ofNat , ←intCast_ofNat aden,
        ←intCast_mul, ←intCast_mul, eq])


class QAlgebraOps (α: Type*) extends FieldOps α, RatCast α, SMul ℚ α where

instance [FieldOps α] [RatCast α] [SMul ℚ α] : QAlgebraOps α where

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

def qsmul_eq_ratCast_mul [QAlgebraOps α] [IsQAlgebra α]: ∀(q: ℚ) (a: α), q • a = q * a := IsQAlgebra.qsmul_eq_ratCast_mul
def ratCast_eq_ratCastRec [QAlgebraOps α] [IsQAlgebra α]: ∀q: ℚ, (q: α) = ratCastRec q := IsQAlgebra.ratCast_eq_ratCastRec
