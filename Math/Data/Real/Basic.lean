import Math.Data.CauchySeq.Completion.Basic
import Math.Algebra.QAlgebra.Basic
import Math.Algebra.Field.Hom
import Math.Data.Rat.Order

-- The reals are the completion of the rationals
def Real := Cauchy ℚ

namespace Real

open IsQAlgebra.ofAlgebra

notation "ℝ" => Real

instance : FieldOps ℝ := inferInstanceAs (FieldOps (Cauchy ℚ))
instance : IsField ℝ := inferInstanceAs (IsField (Cauchy ℚ))
instance : SMul ℚ ℝ := inferInstanceAs (SMul ℚ (Cauchy ℚ))
instance : AlgebraMap ℚ ℝ := inferInstanceAs (AlgebraMap ℚ (Cauchy ℚ))
instance : IsAlgebra ℚ ℝ := inferInstanceAs (IsAlgebra ℚ (Cauchy ℚ))
instance : Inhabited ℝ := ⟨0⟩
instance : Nonempty ℝ := inferInstance

def ofRatHom : ℚ ↪+* ℝ := {
  algebraMap (R := ℚ) with
  inj' := field_hom_inj algebraMap
}

instance : HasChar ℝ 0 := inferInstance
instance : RatCast ℝ := inferInstance
instance : IsQAlgebra ℝ := inferInstance

end Real
