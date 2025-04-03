import Math.Algebra.Hom

section Prod

variable {α β: Type*}

instance [Zero α] [Zero β] : Zero (α × β) where
  zero := (0, 0)
instance [One α] [One β] : One (α × β) where
  one := (1, 1)
instance [NatCast α] [NatCast β] : NatCast (α × β) where
  natCast n := (n, n)
instance [IntCast α] [IntCast β] : IntCast (α × β) where
  intCast n := (n, n)

instance [Add α] [Add β] : Add (α × β) where
  add f g := (f.1 + g.1, f.2 + g.2)

instance [Sub α] [Sub β] : Sub (α × β) where
  sub f g := (f.1 - g.1, f.2 - g.2)

instance [Mul α] [Mul β] : Mul (α × β) where
  mul f g := (f.1 * g.1, f.2 * g.2)

instance [Div α] [Div β] : Div (α × β) where
  div f g := (f.1 / g.1, f.2 / g.2)

instance [SMul R α] [SMul R β] : SMul R (α × β) where
  smul n f := (n • f.1, n • f.2)

instance [Pow α ℕ] [Pow β ℕ] : Pow (α × β) ℕ where
  pow f n := (f.1 ^ n, f.2 ^ n)

instance [Pow α ℤ] [Pow β ℤ] : Pow (α × β) ℤ where
  pow f n := (f.1 ^ n, f.2 ^ n)

instance [Neg α] [Neg β] : Neg (α × β) where
  neg f := (-f.1, -f.2)

instance [Inv α] [Inv β] : Inv (α × β) where
  inv f := (f.1⁻¹, f.2⁻¹)

instance [Zero α] [Zero β] [Add α] [Add β] [IsAddZeroClass α] [IsAddZeroClass β] : IsAddZeroClass (α × β) where
  zero_add := by
    intro f; ext <;> apply zero_add
  add_zero := by
    intro f; ext <;> apply add_zero

instance [One α] [One β] [Mul α] [Mul β] [IsMulOneClass α] [IsMulOneClass β] : IsMulOneClass (α × β)
  := inferInstanceAs (IsMulOneClass (MulOfAdd (AddOfMul α × AddOfMul β)))

instance [Zero α] [Zero β] [Mul α] [Mul β] [IsMulZeroClass α] [IsMulZeroClass β] : IsMulZeroClass (α × β) where
  zero_mul := by
    intro f; ext <;> apply zero_mul
  mul_zero := by
    intro f; ext <;> apply mul_zero

instance [Add α] [Add β] [IsAddSemigroup α] [IsAddSemigroup β] : IsAddSemigroup (α × β) where
  add_assoc := by
    intro a b c; ext <;> apply add_assoc

instance [Mul α] [Mul β] [IsSemigroup α] [IsSemigroup β] : IsSemigroup (α × β) :=
  inferInstanceAs (IsSemigroup (MulOfAdd (AddOfMul α × AddOfMul β)))

instance [Add α] [Add β] [IsAddCommMagma α] [IsAddCommMagma β] : IsAddCommMagma (α × β) where
  add_comm := by
    intro a b; ext <;> apply add_comm

instance [Mul α] [Mul β] [IsCommMagma α] [IsCommMagma β] : IsCommMagma (α × β) :=
  inferInstanceAs (IsCommMagma (MulOfAdd (AddOfMul α × AddOfMul β)))

instance [AddMonoidOps α] [AddMonoidOps β] [IsAddMonoid α] [IsAddMonoid β] : IsAddMonoid (α × β) where
  zero_nsmul := by
    intro f; ext <;>
    apply zero_nsmul
  succ_nsmul := by
    intro n f; ext <;>
    apply succ_nsmul

instance [MonoidOps α] [MonoidOps β] [IsMonoid α] [IsMonoid β] : IsMonoid (α × β)  :=
  inferInstanceAs (IsMonoid (MulOfAdd (AddOfMul α × AddOfMul β)))

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

instance [AddMonoidWithOneOps α] [AddMonoidWithOneOps β] [IsAddMonoidWithOne α] [IsAddMonoidWithOne β] : IsAddMonoidWithOne (α × β) where
  natCast_zero := by ext <;> apply natCast_zero
  natCast_succ := by intro n; ext <;> apply natCast_succ

instance [AddGroupWithOneOps α] [AddGroupWithOneOps β] [IsAddGroupWithOne α] [IsAddGroupWithOne β] : IsAddGroupWithOne (α × β) where
  intCast_ofNat := fun n => by ext <;> apply intCast_ofNat
  intCast_negSucc := fun n => by ext <;> apply intCast_negSucc
  natCast_zero := natCast_zero
  natCast_succ := natCast_succ

instance [Add α] [Add β] [Mul α] [Mul β] [IsLeftDistrib α] [IsLeftDistrib β] : IsLeftDistrib (α × β) where
  left_distrib := by
    intro k a b; ext <;>
    apply mul_add

instance [Add α] [Add β] [Mul α] [Mul β] [IsRightDistrib α] [IsRightDistrib β] : IsRightDistrib (α × β) where
  right_distrib := by
    intro k a b; ext <;>
    apply add_mul

instance [SemiringOps α] [SemiringOps β] [h: IsSemiring α] [g: IsSemiring β] : IsSemiring (α × β) := IsSemiring.inst
instance [RingOps α] [RingOps β] [IsRing α] [IsRing β] : IsRing (α × β) := IsRing.inst

instance [MonoidOps R] [SMul R α] [SMul R β] [IsMonoid R] [IsMulAction R α] [IsMulAction R β] : IsMulAction R (α × β) where
  one_smul := by
    intro a
    ext <;> apply one_smul
  mul_smul := by
    intro r₀ r₁ a
    ext <;> apply mul_smul

instance [MonoidOps R] [SMul R α] [SMul R β] [IsMonoid R]
  [AddMonoidOps α] [AddMonoidOps β] [IsAddMonoid α] [IsAddMonoid β]
  [IsDistribMulAction R α] [IsDistribMulAction R β] : IsDistribMulAction R (α × β) where
  smul_zero := by
    intro a; ext <;> apply smul_zero
  smul_add := by
    intro r a b; ext <;> apply smul_add

instance [SemiringOps R] [SMul R α] [SMul R β] [IsSemiring R]
  [AddMonoidOps α] [AddMonoidOps β] [IsAddMonoid α] [IsAddMonoid β]
  [IsAddCommMagma α] [IsAddCommMagma β]
  [IsModule R α] [IsModule R β] : IsModule R (α × β) where
  add_smul := by
    intro r s a
    ext <;> apply add_smul
  zero_smul := by
    intro r
    ext <;> apply zero_smul

structure Prod.fstHomType (α β: Type*) where
structure Prod.sndHomType (α β: Type*) where

def Prod.fstHom : Prod.fstHomType α β := fstHomType.mk
def Prod.sndHom : Prod.sndHomType α β := sndHomType.mk

instance : FunLike (Prod.fstHomType (α := α) (β := β)) (α × β) α where
  coe _ := Prod.fst
  coe_inj := by intro a b h; rfl

instance : FunLike (Prod.sndHomType (α := α) (β := β)) (α × β) β where
  coe _ := Prod.snd
  coe_inj := by intro a b h; rfl

instance [Zero α] [Zero β] : IsZeroHom (Prod.fstHomType (α := α) (β := β)) (α × β) α where
  map_zero _ := rfl
instance [Zero α] [Zero β] : IsZeroHom (Prod.sndHomType (α := α) (β := β)) (α × β) β where
  map_zero _ := rfl

instance [One α] [One β] : IsOneHom (Prod.fstHomType (α := α) (β := β)) (α × β) α where
  map_one _ := rfl
instance [One α] [One β] : IsOneHom (Prod.sndHomType (α := α) (β := β)) (α × β) β where
  map_one _ := rfl

instance [Add α] [Add β] : IsAddHom (Prod.fstHomType (α := α) (β := β)) (α × β) α where
  map_add _ := rfl
instance [Add α] [Add β] : IsAddHom (Prod.sndHomType (α := α) (β := β)) (α × β) β where
  map_add _ := rfl

instance [Mul α] [Mul β] : IsMulHom (Prod.fstHomType (α := α) (β := β)) (α × β) α where
  map_mul _ := rfl
instance [Mul α] [Mul β] : IsMulHom (Prod.sndHomType (α := α) (β := β)) (α × β) β where
  map_mul _ := rfl

instance [SMul R α] [SMul R β] : IsSMulHom (Prod.fstHomType (α := α) (β := β)) R (α × β) α where
  map_smul _ := rfl
instance [SMul R α] [SMul R β] : IsSMulHom (Prod.sndHomType (α := α) (β := β)) R (α × β) β where
  map_smul _ := rfl

instance [Subsingleton β] : EmbeddingLike (Prod.fstHomType (α := α) (β := β)) (α × β) α where
  coe h := {
    toFun := h
    inj' := by
      intro a b h
      ext
      assumption
      apply Subsingleton.allEq
  }
  coe_inj := by
    intro f a b
    rfl

instance [Subsingleton α] : EmbeddingLike (Prod.sndHomType (α := α) (β := β)) (α × β) β where
  coe h := {
    toFun := h
    inj' := by
      intro a b h
      ext
      apply Subsingleton.allEq
      assumption
  }
  coe_inj := by
    intro f a b
    rfl

end Prod
