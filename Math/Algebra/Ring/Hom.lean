import Math.Algebra.AddGroupWithOne.Hom
import Math.Algebra.Semiring.Hom
import Math.Algebra.Ring.Defs

instance [RingOps R] [IsRing R] : Subsingleton (ℤ →+* R) where
  allEq := by
    intro a b; ext n
    show a (Int.cast n) = b (Int.cast n)
    rw [map_intCast, map_intCast]
