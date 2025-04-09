import Math.Algebra.Monoid.Impls.Pi
import Math.Algebra.Group.Defs

section Pi

variable {ι: Type*} {α: ι -> Type*}

instance [∀i, Neg (α i)] [∀i, IsInvolutiveNeg (α i)] : IsInvolutiveNeg (∀i, α i) where
  neg_neg := by
    intro f; ext i
    apply neg_neg

instance [∀i, Inv (α i)] [∀i, IsInvolutiveInv (α i)] : IsInvolutiveInv (∀i, α i)  :=
  inferInstanceAs (IsInvolutiveInv (MulOfAdd (∀i, AddOfMul (α i))))

instance [∀i, AddGroupOps (α i)] [∀i, IsSubNegMonoid (α i)] : IsSubNegMonoid (∀i, α i) where
  sub_eq_add_neg := by
    intro a b; ext i
    apply sub_eq_add_neg
  zsmul_ofNat := by
    intro n a; ext i
    apply zsmul_ofNat
  zsmul_negSucc := by
    intro n a; ext i
    apply zsmul_negSucc

instance [∀i, GroupOps (α i)] [∀i, IsDivInvMonoid (α i)] : IsDivInvMonoid (∀i, α i)  :=
  inferInstanceAs (IsDivInvMonoid (MulOfAdd (∀i, AddOfMul (α i))))

instance [∀i, AddGroupOps (α i)] [∀i, IsSubtractionMonoid (α i)] : IsSubtractionMonoid (∀i, α i) where
  neg_add_rev := by
    intro a b; ext i
    apply neg_add_rev
  neg_eq_of_add_left := by
    intro a b eq; ext i
    apply neg_eq_of_add_left
    apply congrFun eq

instance [∀i, GroupOps (α i)] [∀i, IsDivisionMonoid (α i)] : IsDivisionMonoid (∀i, α i)  :=
  inferInstanceAs (IsDivisionMonoid (MulOfAdd (∀i, AddOfMul (α i))))

instance [∀i, AddGroupOps (α i)] [∀i, IsAddGroup (α i)] : IsAddGroup (∀i, α i) where
  neg_add_cancel := by
    intro a; ext i
    apply neg_add_cancel

instance [∀i, GroupOps (α i)] [∀i, IsGroup (α i)] : IsGroup (∀i, α i)  :=
  inferInstanceAs (IsGroup (MulOfAdd (∀i, AddOfMul (α i))))

end Pi

section Function

variable {ι: Type*} {α: Type*}

instance [Neg α] [IsInvolutiveNeg α] : IsInvolutiveNeg (ι -> α) :=
  inferInstance
instance [Inv α] [IsInvolutiveInv α] : IsInvolutiveInv (ι -> α)  :=
  inferInstance
instance [AddGroupOps α] [IsSubNegMonoid α] : IsSubNegMonoid (ι -> α) :=
  inferInstance
instance [GroupOps α] [IsDivInvMonoid α] : IsDivInvMonoid (ι -> α)  :=
  inferInstance
instance [AddGroupOps α] [IsSubtractionMonoid α] : IsSubtractionMonoid (ι -> α) :=
  inferInstance
instance [GroupOps α] [IsDivisionMonoid α] : IsDivisionMonoid (ι -> α)  :=
  inferInstance
instance [AddGroupOps α] [IsAddGroup α] : IsAddGroup (ι -> α) :=
  inferInstance
instance [GroupOps α] [IsGroup α] : IsGroup (ι -> α) :=
  inferInstance

end Function
