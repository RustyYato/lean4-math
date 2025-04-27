import Math.Algebra.Con.Defs
import Math.Relation.Defs
import Math.Algebra.Semigroup.Defs

variable {C α: Type*} [RelLike C α] (c: C)

instance AlgQuotient.instIsAddCommMagma [Add α] [IsAddCon C] [IsAddCommMagma α] : IsAddCommMagma (AlgQuotient c) where
  add_comm := by
    intro a b
    induction a with | mk a =>
    induction b with | mk b =>
    apply Quotient.sound
    rw [add_comm]

instance AlgQuotient.instIsCommMagma [Mul α] [IsMulCon C] [IsCommMagma α] : IsCommMagma (AlgQuotient c) where
  mul_comm _ _ := add_comm (α := (AlgQuotient (AddOfMul.mk c))) _ _

instance AlgQuotient.instIsAddSemigroup [Add α] [IsAddCon C] [IsAddSemigroup α] : IsAddSemigroup (AlgQuotient c) where
  add_assoc := by
    intro x y z
    induction x with | mk x =>
    induction y with | mk y =>
    induction z with | mk z =>
    apply Quotient.sound
    rw [add_assoc]

instance AlgQuotient.instIsSemigroup [Mul α] [IsMulCon C] [IsSemigroup α] : IsSemigroup (AlgQuotient c) where
  mul_assoc := add_assoc (α := (AlgQuotient (AddOfMul.mk c)))

instance AlgQuotient.instIsAddZeroClass [Zero α] [Add α] [IsAddCon C] [IsAddZeroClass α] : IsAddZeroClass (AlgQuotient c) where
  add_zero x := by
    induction x with | mk x =>
    apply Quotient.sound
    rw [add_zero]
  zero_add x := by
    induction x with | mk x =>
    apply Quotient.sound
    rw [zero_add]

instance AlgQuotient.instIsMulZeroClass [Zero α] [Mul α] [IsMulCon C] [IsMulZeroClass α] : IsMulZeroClass (AlgQuotient c) where
  mul_zero x := by
    induction x with | mk x =>
    apply Quotient.sound
    rw [mul_zero]
  zero_mul x := by
    induction x with | mk x =>
    apply Quotient.sound
    rw [zero_mul]

instance AlgQuotient.instIsMulOneClass [One α] [Mul α] [IsMulCon C] [IsMulOneClass α] : IsMulOneClass (AlgQuotient c) where
  mul_one := add_zero (α := (AlgQuotient (AddOfMul.mk c)))
  one_mul := zero_add (α := (AlgQuotient (AddOfMul.mk c)))
