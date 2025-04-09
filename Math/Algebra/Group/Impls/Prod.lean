import Math.Algebra.Monoid.Impls.Prod
import Math.Algebra.Group.Defs

instance [Neg α] [Neg β] [IsInvolutiveNeg α] [IsInvolutiveNeg β] : IsInvolutiveNeg (α × β) where
  neg_neg := by
    intro f; ext <;>
    apply neg_neg

instance [Inv α] [Inv β] [IsInvolutiveInv α] [IsInvolutiveInv β] : IsInvolutiveInv (α × β)  :=
  inferInstanceAs (IsInvolutiveInv (MulOfAdd (AddOfMul α × AddOfMul β)))

instance [AddGroupOps α] [AddGroupOps β] [IsSubNegMonoid α] [IsSubNegMonoid β] : IsSubNegMonoid (α × β) where
  sub_eq_add_neg := by
    intro a b; ext <;>
    apply sub_eq_add_neg
  zsmul_ofNat := by
    intro n a; ext <;>
    apply zsmul_ofNat
  zsmul_negSucc := by
    intro n a; ext <;>
    apply zsmul_negSucc

instance [GroupOps α] [GroupOps β] [IsDivInvMonoid α] [IsDivInvMonoid β] : IsDivInvMonoid (α × β)  :=
  inferInstanceAs (IsDivInvMonoid (MulOfAdd (AddOfMul α × AddOfMul β)))

instance [AddGroupOps α] [AddGroupOps β] [IsSubtractionMonoid α] [IsSubtractionMonoid β] : IsSubtractionMonoid (α × β) where
  neg_add_rev := by
    intro a b; ext <;>
    apply neg_add_rev
  neg_eq_of_add_left := by
    intro a b eq
    have ⟨_, _⟩  := Prod.mk.inj eq
    ext <;> (apply neg_eq_of_add_left; assumption)

instance [GroupOps α] [GroupOps β] [IsDivisionMonoid α] [IsDivisionMonoid β] : IsDivisionMonoid (α × β)  :=
  inferInstanceAs (IsDivisionMonoid (MulOfAdd (AddOfMul α × AddOfMul β)))

instance [AddGroupOps α] [AddGroupOps β] [IsAddGroup α] [IsAddGroup β] : IsAddGroup (α × β) where
  neg_add_cancel := by
    intro a; ext <;>
    apply neg_add_cancel

instance [GroupOps α] [GroupOps β] [IsGroup α] [IsGroup β] : IsGroup (α × β)  :=
  inferInstanceAs (IsGroup (MulOfAdd (AddOfMul α × AddOfMul β)))
