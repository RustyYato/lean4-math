import Math.Algebra.AddMonoidWithOne.Hom
import Math.Algebra.Semiring.Defs

instance [SemiringOps R] [IsSemiring R] : Subsingleton (ℕ →+* R) where
  allEq := by
    intro a b; ext n
    show a (Nat.cast n) = b (Nat.cast n)
    rw [map_natCast, map_natCast]

protected def RingHom.natCast [SemiringOps R] [IsSemiring R] : ℕ →+* R where
  toFun n := n
  map_zero := natCast_zero
  map_add := by intro x y; rw [natCast_add]
  map_one := natCast_one
  map_mul := by intro x y; rw [natCast_mul]

@[simp] def RingHom.apply_natCast [SemiringOps R] [IsSemiring R] (x: ℕ) : RingHom.natCast (R := R) x = x := rfl
