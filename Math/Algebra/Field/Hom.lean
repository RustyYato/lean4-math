import Math.Algebra.Field.Defs
import Math.Algebra.GroupWithZero.Hom
import Math.Algebra.Group.Hom
import Math.Logic.Equiv.Like

section

variable [FieldOps F] [IsNonCommField F] [RingOps R] [IsRing R] [IsNontrivial R]
variable [FunLike α F R] [IsRingHom α F R]

instance : EmbeddingLike α F R where
  coe f := {
    toFun := f
    inj' := by
      suffices ∀x, f x = 0 -> x = 0 by
        intro x y eq
        have  eq' : f x - f y = 0 := by rw [eq, sub_self]
        rw [←map_sub] at eq'
        exact eq_of_sub_eq_zero (this _ eq')
      intro x fx
      apply Classical.byContradiction
      intro h
      have : f x * f (x⁻¹?) = 0 := by rw [fx, zero_mul]
      rw [←map_mul, mul_inv?_cancel, map_one] at this
      exact zero_ne_one _ this.symm
  }
  coe_inj := by
    intro a b h
    simp at h
    apply DFunLike.ext
    intro x
    have : a x = b x := by rw [h]
    assumption

def field_hom_inj (f: α) : Function.Injective f :=
  (f: F ↪ R).inj

end
