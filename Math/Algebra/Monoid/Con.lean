import Math.Algebra.Semigroup.Con
import Math.Algebra.Monoid.Defs
import Math.Algebra.Hom.Defs
import Math.Algebra.Con.Basic

variable {C α: Type*} [RelLike C α] (c: C)

def resp_nsmul [AddMonoidOps α] [IsAddMonoid α] [IsAddCon C] (c: C) (n: ℕ) {a b: α} (h: c a b) : c (n • a) (n • b) := by
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul]
  | succ n ih =>
    rw [succ_nsmul, succ_nsmul]
    apply resp_add
    assumption
    assumption

def resp_npow [MonoidOps α] [IsMonoid α] [IsMulCon C] (c: C) (n: ℕ) {a b: α} (h: c a b) : c (a ^ n) (b ^ n) :=
  resp_nsmul (C := AddOfMul C) c n h

instance [AddMonoidOps α] [IsAddMonoid α] [IsAddCon C] : IsSMulCon C ℕ where
  resp_smul := resp_nsmul

instance [AddMonoidOps α] [IsAddMonoid α] [IsAddCon C] : SMul ℕ (AlgQuotient c) := inferInstance
instance [MonoidOps α] [IsMonoid α] [IsMulCon C] : Pow (AlgQuotient c) ℕ where
  pow := flip <| by
    intro n
    apply Quotient.lift (fun a => IsCon.mkQuot c (a ^ n))
    intro a b h
    apply Quotient.sound
    apply resp_npow
    assumption

instance AlgQuotient.instAddMonoidOps [AddMonoidOps α] [IsAddMonoid α] [IsAddCon C]: AddMonoidOps (AlgQuotient c) := inferInstance

instance AlgQuotient.instIsAddMonoid [AddMonoidOps α] [IsAddMonoid α] [IsAddCon C] : IsAddMonoid (AlgQuotient c) where
  zero_nsmul a := by
    induction a with | mk a =>
    apply Quotient.sound
    rw [zero_nsmul]
  succ_nsmul n a := by
    induction a with | mk a =>
    apply Quotient.sound
    rw [succ_nsmul]

instance AlgQuotient.instMonoidOps [MonoidOps α] [IsMonoid α] [IsMulCon C]: MonoidOps (AlgQuotient c) := inferInstance

instance AlgQuotient.instIsMonoid [MonoidOps α] [IsMonoid α] [IsMulCon C] : IsMonoid (AlgQuotient c) where
  npow_zero := zero_nsmul (α := (AlgQuotient (AddOfMul.mk c)))
  npow_succ := succ_nsmul (α := (AlgQuotient (AddOfMul.mk c)))
