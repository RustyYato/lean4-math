import Math.Algebra.Ring.Order.Defs
import Math.Algebra.Ring.Defs
import Math.Algebra.Module.Defs
import Math.Ops.Abs

class IsLawfulNorm (α: Type*) {β: Type*}
  [Norm α β] [LE β] [LT β] [Min β] [Max β]
  [AddGroupOps α]
  [RingOps β] [IsRing β]
  [IsAddGroup α] [IsAddCommMagma α]
  [SMul β α] [IsModule β α]
  [IsOrderedSemiring β]
  [IsLinearLattice β] where
  norm_zero_iff {a: α}: ‖a‖ = 0 ↔ a = 0
  norm_add_le_add_norm (a b: α): ‖a + b‖ ≤ ‖a‖ + ‖b‖
  norm_smul (b: β) (a: α): ‖b • a‖ = |b| * ‖a‖

section

variable
  [Norm α β] [LE β] [LT β] [Min β] [Max β]
  [AddGroupOps α]
  [RingOps β] [IsRing β]
  [IsAddGroup α] [IsAddCommMagma α]
  [SMul β α] [IsModule β α]
  [IsOrderedSemiring β]
  [IsLinearLattice β] [IsLawfulNorm α]

def norm_zero_iff {a: α}: ‖a‖ = 0 ↔ a = 0 := IsLawfulNorm.norm_zero_iff
def norm_add_le_add_norm (a b: α): ‖a + b‖ ≤ ‖a‖ + ‖b‖ := IsLawfulNorm.norm_add_le_add_norm _ _
def norm_smul (b: β) (a: α): ‖b • a‖ = |b| * ‖a‖ := IsLawfulNorm.norm_smul _ _

def norm_zero : ‖(0: α)‖ = 0 := norm_zero_iff.mpr rfl
def of_norm_eq_zero {x: α} : ‖x‖ = 0 -> x = 0 := norm_zero_iff.mp

end

namespace Norm.ofAbs

variable [LatticeOps α] [RingOps α] [IsRing α] [IsOrderedSemiring α] [IsLinearLattice α]

scoped instance [Neg α] [Max α] : Norm α α where
  norm := abs

private def abs_nonneg (a: α) : 0 ≤ |a| := by
  apply le_max_iff.mpr
  rw (occs := [2]) [←neg_zero]; rw [←neg_le_neg_iff]
  apply le_total

instance : IsLawfulNorm α where
  norm_zero_iff := by
    intro a
    show |a| = 0 ↔ a = 0
    apply Iff.intro
    intro h
    rcases lt_trichotomy a 0 with g | g | g
    have : 0 < |a| := by
      unfold abs
      rw [neg_lt_neg_iff, neg_zero] at g
      apply lt_of_lt_of_le g
      apply le_max_right
    rw [h] at this
    have := lt_irrefl this
    contradiction
    assumption
    have : 0 < |a| := by
      unfold abs
      apply lt_of_lt_of_le g
      apply le_max_left
    rw [h] at this
    have := lt_irrefl this
    contradiction
    intro h
    rw [h]
    unfold abs
    rw [neg_zero, max_self]
  norm_smul b a := by
    rw [smul_eq_mul]
    show |b * a| = |b| * |a|
    unfold abs
    apply le_antisymm
    · apply max_le
      rcases le_total b 0
      · rw (occs := [1]) [←neg_neg (b * a), neg_mul_left, neg_mul_right]
        apply le_trans
        apply mul_le_mul_of_nonneg_left
        apply le_max_right
        exact a
        rw [←neg_zero]; apply neg_le_neg; assumption
        apply mul_le_mul_of_nonneg_right
        apply le_max_right
        apply abs_nonneg
      · apply le_trans
        apply mul_le_mul_of_nonneg_left
        apply le_max_left
        exact -a
        assumption
        apply mul_le_mul_of_nonneg_right
        apply le_max_left
        apply abs_nonneg
      rcases le_total b 0
      · rw [neg_mul_left]
        apply le_trans
        apply mul_le_mul_of_nonneg_left
        apply le_max_left
        exact -a
        rw [←neg_zero]; apply neg_le_neg; assumption
        apply mul_le_mul_of_nonneg_right
        apply le_max_right
        apply abs_nonneg
      · rw [neg_mul_right]
        apply le_trans
        apply mul_le_mul_of_nonneg_left
        apply le_max_right
        exact a
        assumption
        apply mul_le_mul_of_nonneg_right
        apply le_max_left
        apply abs_nonneg
    · apply le_max_iff.mpr
      rcases le_total 0 a <;> rcases le_total 0 b <;> rename_i ha hb
      left; rw [max_eq_left.mpr, max_eq_left.mpr]
      apply neg_le_of_nonneg; assumption
      apply neg_le_of_nonneg; assumption
      right; rw [max_eq_right.mpr, max_eq_left.mpr, neg_mul_left]
      apply neg_le_of_nonneg; assumption
      apply le_neg_of_nonpos; assumption
      right; rw [max_eq_left.mpr, max_eq_right.mpr, neg_mul_right]
      apply le_neg_of_nonpos; assumption
      apply neg_le_of_nonneg; assumption
      left; rw [max_eq_right.mpr, max_eq_right.mpr, ←neg_mul_right, ←neg_mul_left, neg_neg]
      apply le_neg_of_nonpos; assumption
      apply le_neg_of_nonpos; assumption
  norm_add_le_add_norm a b := by
    apply max_le
    apply add_le_add
    apply le_max_left
    apply le_max_left
    rw [neg_add_rev, add_comm]
    apply add_le_add
    apply le_max_right
    apply le_max_right

end Norm.ofAbs

def abs_eq_natAbs (a: Int) : |a| = a.natAbs := by
  apply le_antisymm
  apply max_le
  omega
  omega
  apply le_max_iff.mpr
  omega
