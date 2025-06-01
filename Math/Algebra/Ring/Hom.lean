import Math.Algebra.AddGroupWithOne.Hom
import Math.Algebra.Semiring.Hom
import Math.Algebra.Ring.Defs

instance [RingOps R] [IsRing R] : Subsingleton (ℤ →+* R) where
  allEq := by
    intro a b; ext n
    show a (Int.cast n) = b (Int.cast n)
    rw [map_intCast, map_intCast]

protected def RingHom.intCast [RingOps R] [IsRing R] : ℤ →+* R where
  toFun n := n
  map_zero := intCast_zero
  map_add := by intro x y; rw [intCast_add]
  map_one := intCast_one
  map_mul := by intro x y; rw [intCast_mul]

@[simp] def RingHom.apply_intCast [RingOps R] [IsRing R] (x: ℤ) : RingHom.intCast (R := R) x = x := rfl
