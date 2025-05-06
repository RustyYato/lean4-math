import Math.Algebra.AddMonoidWithOne.Hom
import Math.Algebra.Semiring.Defs

instance [SemiringOps R] [IsSemiring R] : Subsingleton (ℕ →+* R) where
  allEq := by
    intro a b; ext n
    show a (Nat.cast n) = b (Nat.cast n)
    rw [map_natCast, map_natCast]
