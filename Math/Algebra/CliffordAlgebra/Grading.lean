import Math.Data.ZMod.Defs
import Math.Algebra.GradedMonoid.Internal
import Math.Algebra.CliffordAlgebra.Defs
import Math.Algebra.Module.SetLike.Defs

namespace CliffordAlgebra

variable [SemiringOps R] [IsSemiring R] [IsCommMagma R] [AddMonoidOps V]
  [IsAddMonoid V] [IsAddCommMagma V] [SMul R V] [IsModule R V]

variable (Q: QuadraticForm R V)

inductive Grading : ZMod 2 -> CliffordAlgebra Q -> Prop where
| zero : Grading i 0
| scalar (x: R) : Grading 0 (algebraMap x)
| vector (x: V) : Grading 1 (ι Q x)
| mul (i j: ZMod 2) (a b: CliffordAlgebra Q) :
  Grading i a -> Grading j b -> Grading (i + j) (a * b)
| add (i: ZMod 2) (a b: CliffordAlgebra Q) :
  Grading i a -> Grading i b -> Grading i (a + b)

def grading (i: ZMod 2) : Submodule R (CliffordAlgebra Q) where
  carrier := Set.mk (Grading Q i)
  mem_zero := Grading.zero
  mem_add := by
    intro a b
    apply Grading.add i
  mem_smul' := by
    intro r a h
    rw [smul_def]
    simp
    rw [←zero_add i]
    apply Grading.mul
    apply Grading.scalar
    assumption

def grading_type : ZMod 2 -> Type _ := (grading Q ·)

instance : SetLike.GradedOne (grading Q) where
  mem_one := by
    rw [←map_one (algebraMap (R := R))]
    apply Grading.scalar
instance : SetLike.GradedMul (grading Q) where
  mem_mul := by
    intro i j a b
    apply Grading.mul

instance : GMonoidOps (grading_type Q) := SetLike.instGMonoidOps (grading Q)
instance : IsGMonoid (grading_type Q) := SetLike.instIsGMonoid (grading Q)
abbrev Graded := GradedMonoid (grading_type Q)

end CliffordAlgebra
