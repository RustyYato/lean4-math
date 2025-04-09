import Math.Algebra.Semigroup.Impls.Bool
import Math.Algebra.Monoid.Defs

instance : IsAddMonoid Bool where
  zero_nsmul := by decide
  succ_nsmul n a := by
    match n with
    | 0 =>
      show 1 * _ = 0 * a + a
      decide +revert
    | n + 1 =>
      show 1 * _ = 1 * a + a
      decide +revert

instance : IsMonoid Bool where
  npow_zero := by decide
  npow_succ n a := by
    show a = min _ _
    cases a
    rw [Bool.min_eq_and, Bool.and_false]
    rw [Bool.min_eq_and, Bool.and_true]
    rw [Bool.npow_def, Bool.or_true]
