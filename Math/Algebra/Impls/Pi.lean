import Math.Algebra.Ring.Defs
import Math.Algebra.Module.Defs

section Pi

variable {ι: Type*} {β: ι -> Type*}

instance [∀i, Zero (β i)] : Zero (∀i, β i) where
  zero _ := 0
instance [∀i, One (β i)] : One (∀i, β i) where
  one _ := 1
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

instance [∀i, SMul R (β i)] : SMul R (∀i, β i) where
  smul n f i := n • f i

instance [∀i, Pow (β i) ℕ] : Pow (∀i, β i) ℕ where
  pow f n i := f i ^ n

instance [∀i, Pow (β i) ℤ] : Pow (∀i, β i) ℤ where
  pow f n i := f i ^ n

instance [∀i, Neg (β i)] : Neg (∀i, β i) where
  neg f i := -f i

instance [∀i, Inv (β i)] : Inv (∀i, β i) where
  inv f i := (f i)⁻¹

def Pi.zero_eq [∀i, Zero (β i)] : (0: ∀i, β i) = fun _ => 0 := rfl
def Pi.one_eq [∀i, One (β i)] : (1: ∀i, β i) = fun _ => 1 := rfl
def Pi.natCast_eq [∀i, NatCast (β i)] (n: ℕ): (n: ∀i, β i) = fun _ => (n: β _) := rfl
def Pi.intCast_eq [∀i, IntCast (β i)] (n: ℤ): (n: ∀i, β i) = fun _ => (n: β _) := rfl
def Pi.add_eq [∀i, Add (β i)] (f g: ∀i, β i): f + g = fun x => f x + g x := rfl
def Pi.mul_eq [∀i, Mul (β i)] (f g: ∀i, β i): f * g = fun x => f x * g x := rfl
def Pi.sub_eq [∀i, Sub (β i)] (f g: ∀i, β i): f - g = fun x => f x - g x := rfl
def Pi.div_eq [∀i, Div (β i)] (f g: ∀i, β i): f / g = fun x => f x / g x := rfl
def Pi.smul_eq [∀i, SMul R (β i)] (r: R) (f: ∀i, β i): r • f = fun x => r • f x := rfl
def Pi.npow_eq [∀i, Pow (β i) ℕ] (f: ∀i, β i) (n: ℕ): f ^ n = fun x => f x ^ n := rfl
def Pi.zpow_eq [∀i, Pow (β i) ℤ] (f: ∀i, β i) (n: ℤ): f ^ n = fun x => f x ^ n := rfl
def Pi.neg_eq [∀i, Neg (β i)] (f: ∀i, β i): -f = fun x => -f x := rfl
def Pi.inv_eq [∀i, Inv (β i)] (f: ∀i, β i): f⁻¹ = fun x => (f x)⁻¹ := rfl

@[simp] def Pi.apply_zero [∀i, Zero (β i)] (i: ι) : (0: ∀i, β i) i = 0 := rfl
@[simp] def Pi.apply_one [∀i, One (β i)] (i: ι) : (1: ∀i, β i) i = 1 := rfl
@[simp] def Pi.apply_natCast [∀i, NatCast (β i)] (n: ℕ) (i: ι): (n: ∀i, β i) i = (n: β _) := rfl
@[simp] def Pi.apply_intCast [∀i, IntCast (β i)] (n: ℤ) (i: ι): (n: ∀i, β i) i = (n: β _) := rfl
@[simp] def Pi.apply_add [∀i, Add (β i)] (f g: ∀i, β i) (i: ι): (f + g) i = f i + g i := rfl
@[simp] def Pi.apply_mul [∀i, Mul (β i)] (f g: ∀i, β i) (i: ι): (f * g) i = f i * g i := rfl
@[simp] def Pi.apply_sub [∀i, Sub (β i)] (f g: ∀i, β i) (i: ι): (f - g) i = f i - g i := rfl
@[simp] def Pi.apply_div [∀i, Div (β i)] (f g: ∀i, β i) (i: ι): (f / g) i = f i / g i := rfl
@[simp] def Pi.apply_smul [∀i, SMul R (β i)] (r: R) (f: ∀i, β i): (r • f) i = r • f i := rfl
@[simp] def Pi.apply_npow [∀i, Pow (β i) ℕ] (f: ∀i, β i) (n: ℕ): (f ^ n) i = f i ^ n := rfl
@[simp] def Pi.apply_zpow [∀i, Pow (β i) ℤ] (f: ∀i, β i) (n: ℤ): (f ^ n) i = f i ^ n := rfl
@[simp] def Pi.apply_neg [∀i, Neg (β i)] (f: ∀i, β i): (-f) i = -f i := rfl
@[simp] def Pi.apply_inv [∀i, Inv (β i)] (f: ∀i, β i): (f⁻¹) i = (f i)⁻¹ := rfl

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

instance [∀i, AddGroupWithOneOps (β i)] [∀i, IsAddGroupWithOne (β i)] : IsAddGroupWithOne (∀i, β i) where
  intCast_ofNat := fun n => by ext; apply intCast_ofNat
  intCast_negSucc := fun n => by ext; apply intCast_negSucc
  natCast_zero := natCast_zero
  natCast_succ := natCast_succ

instance [∀i, Add (β i)] [∀i, Mul (β i)] [∀i, IsLeftDistrib (β i)] : IsLeftDistrib (∀i, β i) where
  mul_add := by
    intro k a b; ext i
    apply mul_add

instance [∀i, Add (β i)] [∀i, Mul (β i)] [∀i, IsRightDistrib (β i)] : IsRightDistrib (∀i, β i) where
  add_mul := by
    intro k a b; ext i
    apply add_mul

instance [∀i, SemiringOps (β i)] [∀i, IsSemiring (β i)] : IsSemiring (∀i, β i) := IsSemiring.inst
instance [∀i, RingOps (β i)] [∀i, IsRing (β i)] : IsRing (∀i, β i) := IsRing.inst

instance [MonoidOps R] [∀i, SMul R (β i)] [IsMonoid R] [∀i, IsMulAction R (β i)] : IsMulAction R (∀i, β i) where
  one_smul := by
    intro a
    ext i; apply one_smul
  mul_smul := by
    intro r₀ r₁ a
    ext i; apply mul_smul

instance [MonoidOps R] [∀i, SMul R (β i)] [IsMonoid R]
  [∀i, AddMonoidOps (β i)] [∀i, IsAddMonoid (β i)]
  [∀i, IsDistribMulAction R (β i)] : IsDistribMulAction R (∀i, β i) where
  smul_zero := by
    intro a; ext i; apply smul_zero
  smul_add := by
    intro r a b; ext i; apply smul_add

instance [SemiringOps R] [∀i, SMul R (β i)] [IsSemiring R]
  [∀i, AddMonoidOps (β i)] [∀i, IsAddMonoid (β i)]
  [∀i, IsAddCommMagma (β i)] [∀i, IsModule R (β i)] : IsModule R (∀i, β i) where
  add_smul := by
    intro r s a
    ext i; apply add_smul
  zero_smul := by
    intro r
    ext i; apply zero_smul

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

def Function.zero_eq [Zero β] : (0: ι -> β) = fun _ => 0 := rfl
def Function.one_eq [One β] : (1: ι -> β) = fun _ => 1 := rfl
def Function.natCast_eq [NatCast β] (n: ℕ): (n: ι -> β) = fun _ => (n: β) := rfl
def Function.intCast_eq [IntCast β] (n: ℤ): (n: ι -> β) = fun _ => (n: β) := rfl
def Function.add_eq [Add β] (f g: ι -> β): f + g = fun x => f x + g x := rfl
def Function.mul_eq [Mul β] (f g: ι -> β): f * g = fun x => f x * g x := rfl
def Function.sub_eq [Sub β] (f g: ι -> β): f - g = fun x => f x - g x := rfl
def Function.div_eq [Div β] (f g: ι -> β): f / g = fun x => f x / g x := rfl
def Function.smul_eq [SMul R β] (r: R) (f: ι -> β): r • f = fun x => r • f x := rfl
def Function.npow_eq [Pow β ℕ] (f: ι -> β) (n: ℕ): f ^ n = fun x => f x ^ n := rfl
def Function.zpow_eq [Pow β ℤ] (f: ι -> β) (n: ℤ): f ^ n = fun x => f x ^ n := rfl
def Function.neg_eq [Neg β] (f: ι -> β): -f = fun x => -f x := rfl
def Function.inv_eq [Inv β] (f: ι -> β): f⁻¹ = fun x => (f x)⁻¹ := rfl

@[simp] def Function.apply_zero [Zero β] (i: ι) : (0: ι -> β) i = 0 := rfl
@[simp] def Function.apply_one [One β] (i: ι) : (1: ι -> β) i = 1 := rfl
@[simp] def Function.apply_natCast [NatCast β] (n: ℕ) (i: ι): (n: ι -> β) i = (n: β) := rfl
@[simp] def Function.apply_intCast [IntCast β] (n: ℤ) (i: ι): (n: ι -> β) i = (n: β) := rfl
@[simp] def Function.apply_add [Add β] (f g: ι -> β) (i: ι): (f + g) i = f i + g i := rfl
@[simp] def Function.apply_mul [Mul β] (f g: ι -> β) (i: ι): (f * g) i = f i * g i := rfl
@[simp] def Function.apply_sub [Sub β] (f g: ι -> β) (i: ι): (f - g) i = f i - g i := rfl
@[simp] def Function.apply_div [Div β] (f g: ι -> β) (i: ι): (f / g) i = f i / g i := rfl
@[simp] def Function.apply_smul [SMul R β] (r: R) (f: ι -> β): (r • f) i = r • f i := rfl
@[simp] def Function.apply_npow [Pow β ℕ] (f: ι -> β) (n: ℕ): (f ^ n) i = f i ^ n := rfl
@[simp] def Function.apply_zpow [Pow β ℤ] (f: ι -> β) (n: ℤ): (f ^ n) i = f i ^ n := rfl
@[simp] def Function.apply_neg [Neg β] (f: ι -> β): (-f) i = -f i := rfl
@[simp] def Function.apply_inv [Inv β] (f: ι -> β): (f⁻¹) i = (f i)⁻¹ := rfl

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

instance [MonoidOps R] [SMul R β] [IsMonoid R] [IsMulAction R β] : IsMulAction R (ι -> β) := inferInstance
instance [MonoidOps R] [SMul R β] [IsMonoid R]
  [AddMonoidOps β] [IsAddMonoid β]
  [IsDistribMulAction R β] : IsDistribMulAction R (ι -> β) := inferInstance
instance [SemiringOps R] [SMul R β] [IsSemiring R]
  [AddMonoidOps β] [IsAddMonoid β]
  [IsAddCommMagma β] [IsModule R β] : IsModule R (ι -> β) := inferInstance

end Function
