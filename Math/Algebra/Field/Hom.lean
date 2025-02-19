import Math.Algebra.Field.Defs
import Math.Algebra.Group.Hom

variable [FieldOps F] [IsField F] [RingOps R] [IsRing R] [IsNontrivial R]

instance
  [FunLike α F R] [IsZeroHom α F R] [IsOneHom α F R] [IsAddHom α F R] [IsMulHom α F R]
  : IsEmbeddingLike α F R where
  coe_inj f := by
    suffices ∀x, f x = 0 -> x = 0 by
      intro x y eq
      have  eq' : f x - f y = 0 := by rw [eq, sub_self]
      rw [←resp_sub] at eq'
      exact eq_of_sub_eq_zero (this _ eq')
    intro x fx
    apply Classical.byContradiction
    intro h
    have : f x * f (x⁻¹?) = 0 := by rw [fx, zero_mul]
    rw [←resp_mul, mul_inv?_cancel, resp_one] at this
    exact zero_ne_one _ this.symm

def field_hom_inj (f: F →+* R) : Function.Injective f :=
  IsEmbeddingLike.coe_inj f
