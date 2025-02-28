import Math.Data.Poly.Basic
import Math.Algebra.Ring.Theory.Ideal.TwoSided.Quotient

open Poly

def xsq_p1_ideal : Ideal (Poly ℤ) := Ideal.generate {X ^ 2 + 1}

def GaussianInteger : Type := xsq_p1_ideal.toRing

namespace GaussianInteger

instance : RingOps GaussianInteger :=
  inferInstanceAs (RingOps xsq_p1_ideal.toRing)
instance : IsRing GaussianInteger :=
  inferInstanceAs (IsRing xsq_p1_ideal.toRing)

-- the imaginary unit
def i := xsq_p1_ideal.mkQuot X

def i_sq : i * i = -1 := by
  refine neg_eq_of_add_right ?_
  apply Quotient.sound
  apply Ideal.Generate.of
  rw [←npow_two, sub_zero]; rfl

end GaussianInteger
