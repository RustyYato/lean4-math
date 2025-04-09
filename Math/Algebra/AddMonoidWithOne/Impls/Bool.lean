import Math.Algebra.Monoid.Impls.Bool
import Math.Algebra.AddMonoidWithOne.Defs

instance : IsAddMonoidWithOne Bool where
  natCast_zero := by rfl
  natCast_succ _ := by
    show true = max _ true
    rw [Bool.max_eq_or, Bool.or_true]
