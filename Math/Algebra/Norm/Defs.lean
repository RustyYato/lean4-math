import Math.Algebra.Ring.Order.Defs
import Math.Algebra.Ring.Defs
import Math.Algebra.Algebra.Defs
import Math.Algebra.Norm.Abs

class IsLawfulNorm (α: Type*) {γ: Type*}
  [Norm α γ] [LatticeOps γ] [SemiringOps γ] [IsSemiring γ]
  [AddGroupOps α] [IsAddGroup α] [IsAddCommMagma α]
  [IsOrderedSemiring γ] [IsLinearLattice γ] where
  norm_zero_iff {a: α}: ‖a‖ = 0 ↔ a = 0
  norm_add_le_add_norm (a b: α): ‖a + b‖ ≤ ‖a‖ + ‖b‖
  -- since we don't include `‖r • a‖ = |r| * ‖a‖`, we include the weaker
  -- axiom, `‖-a‖ = ‖a‖`
  norm_neg (a: α) : ‖-a‖ = ‖a‖

class IsModuleNorm (β α: Type*) {γ: Type*}
  [Norm α γ] [Norm β γ]
  [LatticeOps γ] [SemiringOps γ] [IsSemiring γ]
  [AddGroupOps α] [IsAddGroup α] [IsAddCommMagma α]
  [RingOps β] [IsRing β] [SMul β α] [IsModule β α]
  [IsOrderedSemiring γ] [IsLinearLattice γ]
  [IsLawfulNorm α] [IsLawfulNorm β] where
  norm_smul (b: β) (a: α): ‖b • a‖ = ‖b‖ * ‖a‖

class IsAlgebraNorm (α: Type*) {γ: Type*}
  [Norm α γ] [LatticeOps γ] [SemiringOps γ] [IsSemiring γ]
  [RingOps α] [IsRing α]
  [IsOrderedSemiring γ] [IsLinearLattice γ] extends IsLawfulNorm α where
  norm_one : ‖(1: α)‖ = 1
  norm_mul (a b: α) : ‖a * b‖ = ‖a‖ * ‖b‖

section

variable
  [Norm α γ] [Norm β γ]
  [LatticeOps γ] [SemiringOps γ] [IsSemiring γ]
  [AddGroupOps α] [IsAddGroup α] [IsAddCommMagma α]
  [RingOps β] [IsRing β] [SMul β α] [IsModule β α]
  [IsOrderedSemiring γ] [IsLinearLattice γ]
  [IsLawfulNorm α] [IsLawfulNorm β]

def norm_zero_iff {a: α}: ‖a‖ = 0 ↔ a = 0 := IsLawfulNorm.norm_zero_iff
def norm_add_le_add_norm (a b: α): ‖a + b‖ ≤ ‖a‖ + ‖b‖ := IsLawfulNorm.norm_add_le_add_norm _ _
def norm_neg (a: α): ‖-a‖ = ‖a‖ := IsLawfulNorm.norm_neg _
def norm_smul [IsModuleNorm β α] (b: β) (a: α): ‖b • a‖ = ‖b‖ * ‖a‖ := IsModuleNorm.norm_smul _ _

def norm_zero : ‖(0: α)‖ = 0 := norm_zero_iff.mpr rfl
def of_norm_eq_zero {x: α} : ‖x‖ = 0 -> x = 0 := norm_zero_iff.mp

end

section

variable
  [Norm α γ] [LatticeOps γ] [SemiringOps γ] [IsSemiring γ]
  [RingOps α] [IsRing α]
  [IsOrderedSemiring γ] [IsLinearLattice γ]
  [IsAlgebraNorm α]

def norm_one: ‖(1: α)‖ = 1 := IsAlgebraNorm.norm_one
def norm_mul (a b: α) : ‖a * b‖ = ‖a‖ * ‖b‖ := IsAlgebraNorm.norm_mul _ _

end

namespace Norm.ofAbs

variable [LatticeOps α]
  [RingOps α] [IsRing α] [IsOrderedSemiring α] [IsLinearLattice α]

scoped instance [Neg α] [Max α] : Norm α α where
  norm := abs

instance : IsLawfulNorm α where
  norm_zero_iff {_} := by apply abs_zero_iff
  norm_add_le_add_norm a b := by apply abs_add_le_add_abs
  norm_neg a := by apply abs_neg

instance : IsModuleNorm α α where
  norm_smul b a := by apply abs_mul

instance : IsAlgebraNorm α where
  norm_one := by apply abs_one
  norm_mul := by apply abs_mul

end Norm.ofAbs
