import Math.Algebra.Semiring.SetLike.Basic
import Math.Algebra.Semiring.SetLike.Lattice

namespace Semiring

variable {R: Type*} [SemiringOps R] [IsSemiring R]

structure Center (R: Type*) [SemiringOps R] [IsSemiring R] where

def center (R: Type*) [SemiringOps R] [IsSemiring R] : Center R := Center.mk

instance : SetLike (Center R) R where
  coe _ := Set.mk fun a => ∀x, a * x = x * a
  coe_inj _ _ _ := rfl

@[coe]
def Center.toSubsemiring (_: Center R) : Subsemiring R where
  carrier := Center.mk (R := R)
  mem_zero := by intro x; simp
  mem_one := by intro x; simp
  mem_add := by
    intro a b ha hb x
    rw [add_mul, mul_add, ha, hb]
  mem_mul := by
    intro a b ha hb x
    rw [mul_assoc, hb, ←mul_assoc, ha, mul_assoc]

instance (c: Center R) : SemiringOps c :=
  inferInstanceAs (SemiringOps c.toSubsemiring)
instance (c: Center R) : IsSemiring c :=
  inferInstanceAs (IsSemiring c.toSubsemiring)
instance (c: Center R) : IsCommMagma c where
  mul_comm := by
    intro a b; apply Subtype.val_inj
    apply a.property

instance : Coe (Center R) (Subsemiring R) where
  coe r := Center.toSubsemiring r

def center_eq_top [IsCommMagma R] : (center R: Subsemiring R) = ⊤ := by
  apply le_antisymm (le_top _)
  intro a ha x
  rw [mul_comm]

end Semiring
