import Math.Algebra.Ring.Theory.Basic
import Math.Algebra.Ring.SetLike.Basic
import Math.Algebra.Ring.SetLike.Lattice

namespace Ring

variable [RingOps R] [IsRing R]

-- the center of a ring is the subring of all elements which commute with
-- all other elements of the ring. i.e. the maximum commutative subring
-- of the given ring
def center (R: Type*) [RingOps R] [IsRing R] : Subring R where
  carrier := Set.mk fun r => ∀x: R, r * x = x * r
  mem_zero := by intro x; simp
  mem_one := by intro x; simp
  mem_add := by
    intro a b ha hb x
    rw [add_mul, mul_add, ha, hb ]
  mem_mul := by
    intro a b ha hb x
    rw [mul_assoc, hb, ←mul_assoc, ha, mul_assoc]
  mem_neg := by
    intro a ha x
    rw [neg_mul, ha, mul_neg]

instance : IsCommMagma (center R) where
  mul_comm := by
    intro a b
    apply Subtype.val_inj
    show a.val * b.val = b.val * a.val
    apply a.property

def center_eq_top [IsCommMagma R] : center R = ⊤ := by
  ext i
  apply Iff.intro; intro; trivial
  intro h x
  rw [mul_comm]

end Ring
