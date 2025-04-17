import Math.Algebra.Ring.SetLike.Basic
import Math.Algebra.Ring.SetLike.Lattice
import Math.Algebra.Semiring.Theory.Center

namespace Ring

variable [RingOps R] [IsRing R]

@[coe]
def _root_.Semiring.Center.toSubring (r: Semiring.Center R) : Subring R := {
  Semiring.Center.toSubsemiring r with
  mem_neg := by
    intro a ha x
    simp [ha x]
}

def center (R: Type*) [RingOps R] [IsRing R] : Semiring.Center R := Semiring.center R

instance (c: Semiring.Center R) : RingOps c :=
  inferInstanceAs (RingOps c.toSubring)
instance (c: Semiring.Center R) : IsRing c :=
  inferInstanceAs (IsRing c.toSubring)

instance : Coe (Semiring.Center R) (Subring R) where
  coe r := Semiring.Center.toSubring r

def center_eq_top [IsCommMagma R] : (center R: Subring R) = ⊤ := by
  ext i
  apply Iff.intro; intro; trivial
  intro h x
  rw [mul_comm]

end Ring
