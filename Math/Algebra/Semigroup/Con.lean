import Math.Algebra.Con.Defs
import Math.Relation.Basic
import Math.Algebra.Semigroup.Defs

variable {C α: Type*} [RelLike C α] (c: C)

instance [Add α] [IsAddCon C] [IsAddCommMagma α] : IsAddCommMagma (IsCon.Quotient c) where
  add_comm := by
    intro a b
    induction a with | mk a =>
    induction b with | mk b =>
    apply Quotient.sound
    rw [add_comm]

instance [Mul α] [IsMulCon C] [IsCommMagma α] : IsCommMagma (IsCon.Quotient c) where
  mul_comm := by
    intro a b
    induction a with | mk a =>
    induction b with | mk b =>
    apply Quotient.sound
    rw [mul_comm]

instance [Add α] [IsAddCon C] [IsAddSemigroup α] : IsAddSemigroup (IsCon.Quotient c) where
  add_assoc := by
    intro x y z
    induction x with | mk x =>
    induction y with | mk y =>
    induction z with | mk z =>
    apply Quotient.sound
    rw [add_assoc]

instance [Mul α] [IsMulCon C] [IsSemigroup α] : IsSemigroup (IsCon.Quotient c) where
  mul_assoc := by
    intro x y z
    induction x with | mk x =>
    induction y with | mk y =>
    induction z with | mk z =>
    apply Quotient.sound
    rw [mul_assoc]

instance [Zero α] [Add α] [IsAddCon C] [IsAddZeroClass α] : IsAddZeroClass (IsCon.Quotient c) where
  add_zero x := by
    induction x with | mk x =>
    apply Quotient.sound
    rw [add_zero]
  zero_add x := by
    induction x with | mk x =>
    apply Quotient.sound
    rw [zero_add]

instance [Zero α] [Mul α] [IsMulCon C] [IsMulZeroClass α] : IsMulZeroClass (IsCon.Quotient c) where
  mul_zero x := by
    induction x with | mk x =>
    apply Quotient.sound
    rw [mul_zero]
  zero_mul x := by
    induction x with | mk x =>
    apply Quotient.sound
    rw [zero_mul]

instance [One α] [Mul α] [IsMulCon C] [IsMulOneClass α] : IsMulOneClass (IsCon.Quotient c) where
  mul_one x := by
    induction x with | mk x =>
    apply Quotient.sound
    rw [mul_one]
  one_mul x := by
    induction x with | mk x =>
    apply Quotient.sound
    rw [one_mul]
