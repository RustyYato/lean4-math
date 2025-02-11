import Math.Algebra.Ring

section Pi

variable {ι: Type*} {β: ι -> Type*}

instance [∀i, Zero (β i)] : Zero (∀i, β i) where
  zero _ := 0
instance [∀i, One (β i)] : One (∀i, β i) where
  one _ := 1
instance [∀i, OfNat (β i) (n+2)] : OfNat (∀i, β i) (n+2) where
  ofNat _ := OfNat.ofNat (n+2)
instance [∀i, NatCast (β i)] : NatCast (∀i, β i) where
  natCast n _ := n
instance [∀i, IntCast (β i)] : IntCast (∀i, β i) where
  intCast n _ := n

instance [∀i, Add (β i)] : Add (∀i, β i) where
  add f g i := f i + g i

instance [∀i, Sub (β i)] : Sub (∀i, β i) where
  sub f g i := f i - g i

instance [∀i, Mul (β i)] : Mul (∀i, β i) where
  mul f g i := f i * g i

instance [∀i, Div (β i)] : Div (∀i, β i) where
  div f g i := f i / g i

instance [∀i, SMul ℕ (β i)] : SMul ℕ (∀i, β i) where
  smul n f i := n • f i

instance [∀i, SMul ℤ (β i)] : SMul ℤ (∀i, β i) where
  smul n f i := n • f i

instance [∀i, Pow (β i) ℕ] : Pow (∀i, β i) ℕ where
  pow f n i := f i ^ n

instance [∀i, Pow (β i) ℤ] : Pow (∀i, β i) ℤ where
  pow f n i := f i ^ n

instance [∀i, Neg (β i)] : Neg (∀i, β i) where
  neg f i := -f i

instance [∀i, Inv (β i)] : Inv (∀i, β i) where
  inv f i := (f i)⁻¹

instance [∀i, Zero (β i)] [∀i, Add (β i)] [∀i, IsAddZeroClass (β i)] : IsAddZeroClass (∀i, β i) where
  zero_add := by
    intro f; ext i
    apply zero_add
  add_zero := by
    intro f; ext i
    apply add_zero

instance [∀i, One (β i)] [∀i, Mul (β i)] [∀i, IsMulOneClass (β i)] : IsMulOneClass (∀i, β i)
  := inferInstanceAs (IsMulOneClass (MulOfAdd (∀i, AddOfMul (β i))))

instance [∀i, Zero (β i)] [∀i, Mul (β i)] [∀i, IsMulZeroClass (β i)] : IsMulZeroClass (∀i, β i) where
  zero_mul := by
    intro f; ext i
    apply zero_mul
  mul_zero := by
    intro f; ext i
    apply mul_zero

instance [∀i, Add (β i)] [∀i, IsAddSemigroup (β i)] : IsAddSemigroup (∀i, β i) where
  add_assoc := by
    intro a b c; ext i
    apply add_assoc

instance [∀i, Mul (β i)] [∀i, IsSemigroup (β i)] : IsSemigroup (∀i, β i) :=
  inferInstanceAs (IsSemigroup (MulOfAdd (∀i, AddOfMul (β i))))

instance [∀i, Add (β i)] [∀i, IsAddCommMagma (β i)] : IsAddCommMagma (∀i, β i) where
  add_comm := by
    intro a b; ext i
    apply add_comm

instance [∀i, Mul (β i)] [∀i, IsCommMagma (β i)] : IsCommMagma (∀i, β i) :=
  inferInstanceAs (IsCommMagma (MulOfAdd (∀i, AddOfMul (β i))))

instance [∀i, AddMonoidOps (β i)] [∀i, IsAddMonoid (β i)] : IsAddMonoid (∀i, β i) where
  zero_nsmul := by
    intro f; ext i
    apply zero_nsmul
  succ_nsmul := by
    intro n f; ext i
    apply succ_nsmul

instance [∀i, MonoidOps (β i)] [∀i, IsMonoid (β i)] : IsMonoid (∀i, β i)  :=
  inferInstanceAs (IsMonoid (MulOfAdd (∀i, AddOfMul (β i))))

instance [∀i, Neg (β i)] [∀i, IsInvolutiveNeg (β i)] : IsInvolutiveNeg (∀i, β i) where
  neg_neg := by
    intro f; ext i
    apply neg_neg

instance [∀i, Inv (β i)] [∀i, IsInvolutiveInv (β i)] : IsInvolutiveInv (∀i, β i)  :=
  inferInstanceAs (IsInvolutiveInv (MulOfAdd (∀i, AddOfMul (β i))))

instance [∀i, AddGroupOps (β i)] [∀i, IsSubNegMonoid (β i)] : IsSubNegMonoid (∀i, β i) where
  sub_eq_add_neg := by
    intro a b; ext i
    apply sub_eq_add_neg
  zsmul_ofNat := by
    intro n a; ext i
    apply zsmul_ofNat
  zsmul_negSucc := by
    intro n a; ext i
    apply zsmul_negSucc

instance [∀i, GroupOps (β i)] [∀i, IsDivInvMonoid (β i)] : IsDivInvMonoid (∀i, β i)  :=
  inferInstanceAs (IsDivInvMonoid (MulOfAdd (∀i, AddOfMul (β i))))

instance [∀i, AddGroupOps (β i)] [∀i, IsSubtractionMonoid (β i)] : IsSubtractionMonoid (∀i, β i) where
  neg_add_rev := by
    intro a b; ext i
    apply neg_add_rev
  neg_eq_of_add_left := by
    intro a b eq; ext i
    apply neg_eq_of_add_left
    apply congrFun eq

instance [∀i, GroupOps (β i)] [∀i, IsDivisionMonoid (β i)] : IsDivisionMonoid (∀i, β i)  :=
  inferInstanceAs (IsDivisionMonoid (MulOfAdd (∀i, AddOfMul (β i))))

instance [∀i, AddGroupOps (β i)] [∀i, IsAddGroup (β i)] : IsAddGroup (∀i, β i) where
  neg_add_cancel := by
    intro a; ext i
    apply neg_add_cancel

instance [∀i, GroupOps (β i)] [∀i, IsGroup (β i)] : IsGroup (∀i, β i)  :=
  inferInstanceAs (IsGroup (MulOfAdd (∀i, AddOfMul (β i))))

instance [∀i, AddMonoidWithOneOps (β i)] [∀i, IsAddMonoidWithOne (β i)] : IsAddMonoidWithOne (∀i, β i) where
  natCast_zero := by ext i; apply natCast_zero
  natCast_succ := by intro n; ext i; apply natCast_succ
  ofNat_eq_natCast := by intro n; ext i; apply ofNat_eq_natCast

instance [∀i, AddGroupWithOneOps (β i)] [∀i, IsAddGroupWithOne (β i)] : IsAddGroupWithOne (∀i, β i) where
  intCast_ofNat := fun n => by ext; apply intCast_ofNat
  intCast_negSucc := fun n => by ext; apply intCast_negSucc
  natCast_zero := natCast_zero
  natCast_succ := natCast_succ
  ofNat_eq_natCast := ofNat_eq_natCast

instance [∀i, Add (β i)] [∀i, Mul (β i)] [∀i, IsLeftDistrib (β i)] : IsLeftDistrib (∀i, β i) where
  left_distrib := by
    intro k a b; ext i
    apply left_distrib

instance [∀i, Add (β i)] [∀i, Mul (β i)] [∀i, IsRightDistrib (β i)] : IsRightDistrib (∀i, β i) where
  right_distrib := by
    intro k a b; ext i
    apply right_distrib

instance [∀i, SemiringOps (β i)] [∀i, IsSemiring (β i)] : IsSemiring (∀i, β i) := inferInstance
instance [∀i, RingOps (β i)] [∀i, IsRing (β i)] : IsRing (∀i, β i) := inferInstance

end Pi

-- these instances are needed to get IsRing (ι -> ι -> β)
-- for some reason Lean doesn't infer them from the Pi instances
-- even though all of the below are infered
section Function

variable {ι β: Type*}

instance [Zero β] : Zero (ι -> β) :=
  inferInstance
instance [One β] : One (ι -> β) :=
  inferInstance
instance [OfNat β (n+2)] : OfNat (ι -> β) (n+2) :=
  inferInstance
instance [NatCast β] : NatCast (ι -> β) :=
  inferInstance
instance [IntCast β] : IntCast (ι -> β) :=
  inferInstance
instance [Add β] : Add (ι -> β) :=
  inferInstance
instance [Sub β] : Sub (ι -> β) :=
  inferInstance
instance [Mul β] : Mul (ι -> β) :=
  inferInstance
instance [Div β] : Div (ι -> β) :=
  inferInstance
instance [SMul ℕ β] : SMul ℕ (ι -> β) :=
  inferInstance
instance [SMul ℤ β] : SMul ℤ (ι -> β) :=
  inferInstance
instance [Pow β ℕ] : Pow (ι -> β) ℕ :=
  inferInstance
instance [Pow β ℤ] : Pow (ι -> β) ℤ :=
  inferInstance
instance [Neg β] : Neg (ι -> β) :=
  inferInstance
instance [Inv β] : Inv (ι -> β) :=
  inferInstance

instance [Zero β] [Add β] [IsAddZeroClass β] : IsAddZeroClass (ι -> β) :=
  inferInstance
instance [One β] [Mul β] [IsMulOneClass β] : IsMulOneClass (ι -> β) :=
  inferInstance
instance [Zero β] [Mul β] [IsMulZeroClass β] : IsMulZeroClass (ι -> β) :=
  inferInstance
instance [Add β] [IsAddSemigroup β] : IsAddSemigroup (ι -> β) :=
  inferInstance
instance [Mul β] [IsSemigroup β] : IsSemigroup (ι -> β) :=
  inferInstance
instance [Add β] [IsAddCommMagma β] : IsAddCommMagma (ι -> β) :=
  inferInstance
instance [Mul β] [IsCommMagma β] : IsCommMagma (ι -> β) :=
  inferInstance
instance [AddMonoidOps β] [IsAddMonoid β] : IsAddMonoid (ι -> β) :=
  inferInstance
instance [MonoidOps β] [IsMonoid β] : IsMonoid (ι -> β) :=
  inferInstance
instance [Neg β] [IsInvolutiveNeg β] : IsInvolutiveNeg (ι -> β) :=
  inferInstance
instance [Inv β] [IsInvolutiveInv β] : IsInvolutiveInv (ι -> β)  :=
  inferInstance
instance [AddGroupOps β] [IsSubNegMonoid β] : IsSubNegMonoid (ι -> β) :=
  inferInstance
instance [GroupOps β] [IsDivInvMonoid β] : IsDivInvMonoid (ι -> β)  :=
  inferInstance
instance [AddGroupOps β] [IsSubtractionMonoid β] : IsSubtractionMonoid (ι -> β) :=
  inferInstance
instance [GroupOps β] [IsDivisionMonoid β] : IsDivisionMonoid (ι -> β)  :=
  inferInstance
instance [AddGroupOps β] [IsAddGroup β] : IsAddGroup (ι -> β) :=
  inferInstance
instance [GroupOps β] [IsGroup β] : IsGroup (ι -> β) :=
  inferInstance
instance [AddMonoidWithOneOps β] [IsAddMonoidWithOne β] : IsAddMonoidWithOne (ι -> β) :=
  inferInstance
instance [AddGroupWithOneOps β] [IsAddGroupWithOne β] : IsAddGroupWithOne (ι -> β) :=
  inferInstance
instance [Add β] [Mul β] [IsLeftDistrib β] : IsLeftDistrib (ι -> β) :=
  inferInstance
instance [Add β] [Mul β] [IsRightDistrib β] : IsRightDistrib (ι -> β) :=
  inferInstance
instance [SemiringOps β] [IsSemiring β] : IsSemiring (ι -> β) := inferInstance
instance [RingOps β] [IsRing β] : IsRing (ι -> β) := inferInstance

end Function
