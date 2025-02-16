import Math.Type.Basic
import Math.Algebra.Ring.Defs

section

variable (α β: Type*)
variable [Zero α] [One α] [Add α] [Mul α] [Neg α] [Inv α]
variable [Zero β] [One β] [Add β] [Mul β] [Neg β] [Inv β]

structure ZeroHom where
  toFun: α -> β
  resp_zero: toFun (0: α) = (0: β)

instance : FunLike (ZeroHom α β) α β where
  coe := ZeroHom.toFun
  coe_inj := by
    intro ⟨_, _⟩ ⟨_, _⟩ _
    congr

structure OneHom where
  toFun: α -> β
  resp_one: toFun (1: α) = (1: β)

instance : FunLike (OneHom α β) α β where
  coe := OneHom.toFun
  coe_inj := by
    intro ⟨_, _⟩ ⟨_, _⟩ _
    congr

structure AddHom where
  toFun: α -> β
  resp_add: ∀{x y: α}, toFun (x + y) = toFun x + toFun y

instance : FunLike (AddHom α β) α β where
  coe := AddHom.toFun
  coe_inj := by
    intro ⟨_, _⟩ ⟨_, _⟩ _
    congr

structure MulHom where
  toFun: α -> β
  resp_mul: ∀{x y: α}, toFun (x * y) = toFun x * toFun y

instance : FunLike (MulHom α β) α β where
  coe := MulHom.toFun
  coe_inj := by
    intro ⟨_, _⟩ ⟨_, _⟩ _
    congr

structure NegHom where
  toFun: α -> β
  resp_neg: ∀{x: α}, toFun (-x) = -toFun x

instance : FunLike (NegHom α β) α β where
  coe := NegHom.toFun
  coe_inj := by
    intro ⟨_, _⟩ ⟨_, _⟩ _
    congr

structure InvHom where
  toFun: α -> β
  resp_inv: ∀{x: α}, toFun (x⁻¹) = (toFun x)⁻¹

instance : FunLike (InvHom α β) α β where
  coe := InvHom.toFun
  coe_inj := by
    intro ⟨_, _⟩ ⟨_, _⟩ _
    congr

class ZeroHomClass (F: Type*) (α β: outParam Type*) [Zero α] [Zero β] [FunLike F α β] where
    resp_zero: ∀f: F, f 0 = 0

export ZeroHomClass (resp_zero)

instance : ZeroHomClass (ZeroHom α β) α β := ⟨ZeroHom.resp_zero⟩

class OneHomClass (F: Type*) (α β: outParam Type*) [One α] [One β] [FunLike F α β] where
    resp_one: ∀f: F, f 1 = 1

export OneHomClass (resp_one)

instance : OneHomClass (OneHom α β) α β := ⟨OneHom.resp_one⟩

class AddHomClass (F: Type*) (α β: outParam Type*) [Add α] [Add β] [FunLike F α β] where
    resp_add: ∀f: F, ∀{x y}, f (x + y) = f x + f y

export AddHomClass (resp_add)

instance : AddHomClass (AddHom α β) α β := ⟨AddHom.resp_add⟩

class MulHomClass (F: Type*) (α β: outParam Type*) [Mul α] [Mul β] [FunLike F α β] where
    resp_mul: ∀f: F, ∀{x y}, f (x * y) = f x * f y

export MulHomClass (resp_mul)

instance : MulHomClass (MulHom α β) α β := ⟨MulHom.resp_mul⟩

class NegHomClass (F: Type*) (α β: outParam Type*) [Neg α] [Neg β] [FunLike F α β] where
    resp_neg: ∀f: F, ∀{x}, f (-x) = -f x

export NegHomClass (resp_neg)

instance : NegHomClass (NegHom α β) α β := ⟨NegHom.resp_neg⟩

class InvHomClass (F: Type*) (α β: outParam Type*) [Inv α] [Inv β] [FunLike F α β] where
    resp_inv: ∀f: F, ∀{x}, f x⁻¹ = (f x)⁻¹

export InvHomClass (resp_inv)

instance : NegHomClass (NegHom α β) α β := ⟨NegHom.resp_neg⟩

structure AddGroupHom extends ZeroHom α β, AddHom α β where

instance : FunLike (AddGroupHom α β) α β where
  coe f := f.toFun
  coe_inj := by
    intro f g _; repeat obtain ⟨f, _⟩ := f
    congr

instance : ZeroHomClass (AddGroupHom α β) α β where
  resp_zero f := f.resp_zero

instance : AddHomClass (AddGroupHom α β) α β where
  resp_add f := f.resp_add

structure GroupHom extends OneHom α β, MulHom α β where

instance : FunLike (GroupHom α β) α β where
  coe f := f.toFun
  coe_inj := by
    intro f g _; repeat obtain ⟨f, _⟩ := f
    congr

instance : OneHomClass (GroupHom α β) α β where
  resp_one f := f.resp_one

instance : MulHomClass (GroupHom α β) α β where
  resp_mul f := f.resp_mul

structure RingHom extends AddGroupHom α β, GroupHom α β where

instance : FunLike (RingHom α β) α β where
  coe f := f.toFun
  coe_inj := by
    intro f g _; repeat obtain ⟨f, _⟩ := f
    congr

instance : ZeroHomClass (RingHom α β) α β where
  resp_zero f := f.resp_zero

instance : AddHomClass (RingHom α β) α β where
  resp_add f := f.resp_add

instance : OneHomClass (RingHom α β) α β where
  resp_one f := f.resp_one

instance : MulHomClass (RingHom α β) α β where
  resp_mul f := f.resp_mul

structure AddGroupEmbedding extends α ↪ β, AddGroupHom α β where

instance : FunLike (AddGroupEmbedding α β) α β where
  coe f := f.toFun
  coe_inj := by
    intro f g _; repeat obtain ⟨f, _⟩ := f
    congr

instance : ZeroHomClass (AddGroupEmbedding α β) α β where
  resp_zero f := f.resp_zero

instance : AddHomClass (AddGroupEmbedding α β) α β where
  resp_add f := f.resp_add

structure GroupEmbedding extends α ↪ β, GroupHom α β where

instance : FunLike (GroupEmbedding α β) α β where
  coe f := f.toFun
  coe_inj := by
    intro f g _; repeat obtain ⟨f, _⟩ := f
    congr

instance : OneHomClass (GroupEmbedding α β) α β where
  resp_one f := f.resp_one

instance : MulHomClass (GroupEmbedding α β) α β where
  resp_mul f := f.resp_mul

structure RingEmbedding extends α ↪ β, RingHom α β where

instance : FunLike (RingEmbedding α β) α β where
  coe f := f.toFun
  coe_inj := by
    intro f g _; repeat obtain ⟨f, _⟩ := f
    congr

instance : ZeroHomClass (RingEmbedding α β) α β where
  resp_zero f := f.resp_zero

instance : AddHomClass (RingEmbedding α β) α β where
  resp_add f := f.resp_add

instance : OneHomClass (RingEmbedding α β) α β where
  resp_one f := f.resp_one

instance : MulHomClass (RingEmbedding α β) α β where
  resp_mul f := f.resp_mul

structure AddGroupEquiv extends α ≃ β, AddGroupHom α β where

instance : FunLike (AddGroupEquiv α β) α β where
  coe f := f.toFun
  coe_inj := by
    intro f g _; repeat obtain ⟨f, _⟩ := f
    congr 1
    apply DFunLike.coe_inj
    assumption

instance : ZeroHomClass (AddGroupEquiv α β) α β where
  resp_zero f := f.resp_zero

instance : AddHomClass (AddGroupEquiv α β) α β where
  resp_add f := f.resp_add

structure GroupEquiv extends α ≃ β, GroupHom α β where

instance : FunLike (GroupEquiv α β) α β where
  coe f := f.toFun
  coe_inj := by
    intro f g _; repeat obtain ⟨f, _⟩ := f
    congr 1
    apply DFunLike.coe_inj
    assumption

instance : OneHomClass (GroupEquiv α β) α β where
  resp_one f := f.resp_one

instance : MulHomClass (GroupEquiv α β) α β where
  resp_mul f := f.resp_mul

structure RingEquiv extends α ≃ β, RingHom α β where

instance : FunLike (RingEquiv α β) α β where
  coe f := f.toFun
  coe_inj := by
    intro f g _; repeat obtain ⟨f, _⟩ := f
    congr 1
    apply DFunLike.coe_inj
    assumption

instance : ZeroHomClass (RingEquiv α β) α β where
  resp_zero f := f.resp_zero

instance : AddHomClass (RingEquiv α β) α β where
  resp_add f := f.resp_add

instance : OneHomClass (RingEquiv α β) α β where
  resp_one f := f.resp_one

instance : MulHomClass (RingEquiv α β) α β where
  resp_mul f := f.resp_mul

infixr:25 " →+ " => AddGroupHom
infixr:25 " →* " => GroupHom

infixr:25 " →+* " => RingHom

infixr:25 " ↪+ " => AddGroupEmbedding
infixr:25 " ↪* " => GroupEmbedding

infixr:25 " ↪+* " => RingEmbedding

infixr:25 " ≃+ " => AddGroupEquiv
infixr:25 " ≃* " => GroupEquiv

infixr:25 " ≃+* " => RingEquiv

end

section

section

variable {F α β: Type*} [FunLike F α β]
-- variable [Zero α] [One α] [Add α] [Sub α] [Neg α] [Mul α] [Div α] [Inv α] [SMul ℕ α] [Pow α ℕ] [SMul ℤ α] [Pow α ℤ] [NatCast α] [IntCast α] [∀n, OfNat α (n + 2)]
-- variable [Zero β] [One β] [Add β] [Sub β] [Neg β] [Mul β] [Div β] [Inv β] [SMul ℕ β] [Pow β ℕ] [SMul ℤ β] [Pow β ℤ] [NatCast β] [IntCast β] [∀n, OfNat β (n + 2)]

-- variable [ZeroHomClass F α β] [OneHomClass F α β] [AddHomClass F α β] [MulHomClass F α β]
--   [NegHomClass F α β] [InvHomClass F α β]

@[coe]
def toZeroHom [Zero α] [Zero β] [ZeroHomClass F α β] (f: F): ZeroHom α β where
  toFun := f
  resp_zero := resp_zero f

@[coe]
def toOneHom [One α] [One β] [OneHomClass F α β] (f: F): OneHom α β where
  toFun := f
  resp_one := resp_one f

@[coe]
def toAddHom [Add α] [Add β] [AddHomClass F α β] (f: F): AddHom α β where
  toFun := f
  resp_add := resp_add f

@[coe]
def toMulHom [Mul α] [Mul β] [MulHomClass F α β] (f: F): MulHom α β where
  toFun := f
  resp_mul := resp_mul f

@[coe]
def toNegHom [Neg α] [Neg β] [NegHomClass F α β] (f: F): NegHom α β where
  toFun := f
  resp_neg := resp_neg f

@[coe]
def toInvHom [Inv α] [Inv β] [InvHomClass F α β] (f: F): InvHom α β where
  toFun := f
  resp_inv := resp_inv f

@[coe]
def toAddGroupHom [AddMonoidOps α] [AddMonoidOps β] [ZeroHomClass F α β] [AddHomClass F α β] (f: F) : α →+ β where
  toFun := f
  resp_zero := resp_zero f
  resp_add := resp_add f

@[coe]
def toGroupHom [MonoidOps α] [MonoidOps β] [OneHomClass F α β] [MulHomClass F α β] (f: F) : α →* β where
  toFun := f
  resp_one := resp_one f
  resp_mul := resp_mul f

@[coe]
def toRingHom [SemiringOps α] [SemiringOps β] [ZeroHomClass F α β] [AddHomClass F α β] [OneHomClass F α β] [MulHomClass F α β] (f: F) : α →+* β where
  toFun := f
  resp_one := resp_one f
  resp_mul := resp_mul f
  resp_zero := resp_zero f
  resp_add := resp_add f

private
def ZeroHom.ofOneHom [One α] [One β] (h: OneHom α β) : ZeroHom (AddOfMul α) (AddOfMul β) where
  toFun := h
  resp_zero := h.resp_one

private
def AddHom.ofMulHom [Mul α] [Mul β] (h: MulHom α β) : AddHom (AddOfMul α) (AddOfMul β) where
  toFun := h
  resp_add := h.resp_mul

private
def AddGroupHom.ofGroupHom [MonoidOps α] [MonoidOps β] (h: GroupHom α β) : AddGroupHom (AddOfMul α) (AddOfMul β) where
  toFun := h
  resp_zero := h.resp_one
  resp_add := h.resp_mul

instance
  [AddGroupOps α] [IsAddGroup α] [AddGroupOps β] [IsSubtractionMonoid β]
  [ZeroHomClass F α β] [AddHomClass F α β] : NegHomClass F α β where
  resp_neg := by
    intro f x
    symm; apply neg_eq_of_add_left
    rw [←resp_add, add_neg_cancel, resp_zero]

instance
  [GroupOps α] [IsGroup α] [GroupOps β] [IsDivisionMonoid β]
  [OneHomClass F α β] [MulHomClass F α β] : InvHomClass F α β where
  resp_inv := by
    intro f x
    symm; apply inv_eq_of_mul_left
    rw [←resp_mul, mul_inv_cancel, resp_one]

def resp_nsmul
  [AddMonoidOps α] [AddMonoidOps β]
  [ZeroHomClass F α β] [AddHomClass F α β]
  [IsAddMonoid α] [IsAddMonoid β]
  (f: F) (n: ℕ) (x: α) : f (n • x) = n • f x := by
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul, resp_zero]
  | succ n ih => rw [succ_nsmul, succ_nsmul, resp_add, ih]

def resp_npow
  [MonoidOps α] [MonoidOps β]
  [OneHomClass F α β] [MulHomClass F α β]
  [IsMonoid α] [IsMonoid β]
  (f: F) (n: ℕ) (x: α) : f (x ^ n) = (f x) ^ n :=
  resp_nsmul (AddGroupHom.ofGroupHom (toGroupHom f)) n (AddOfMul.mk x)

def resp_zsmul
  [AddGroupOps α] [AddGroupOps β]
  [ZeroHomClass F α β] [AddHomClass F α β] [NegHomClass F α β]
  [IsSubNegMonoid α] [IsSubNegMonoid β]
  (f: F) (n: ℤ) (x: α) : f (n • x) = n • f x := by
  induction n with
  | ofNat n => rw [Int.ofNat_eq_coe, zsmul_ofNat, zsmul_ofNat, resp_nsmul]
  | negSucc n => rw [zsmul_negSucc, zsmul_negSucc, resp_neg, resp_nsmul]

def resp_zpow
  [GroupOps α] [GroupOps β]
  [OneHomClass F α β] [MulHomClass F α β] [InvHomClass F α β]
  [IsDivInvMonoid α] [IsDivInvMonoid β]
  (f: F) (n: ℤ) (x: α) : f (x ^ n) = (f x) ^ n :=  by
  -- can't map to resp_zsmul because that would introduce more restrictive bounds
  -- than I would like to enforce. (would promote to IsGroup α/IsDivisionMonoid β)
  induction n with
  | ofNat n => rw [Int.ofNat_eq_coe, zpow_ofNat, zpow_ofNat, resp_npow]
  | negSucc n => rw [zpow_negSucc, zpow_negSucc, resp_inv, resp_npow]

def resp_sub
  [AddGroupOps α] [AddGroupOps β]
  [ZeroHomClass F α β] [AddHomClass F α β] [NegHomClass F α β]
  [IsSubNegMonoid α] [IsSubNegMonoid β]
  (f: F) {x y: α} : f (x - y) = f x - f y := by
  rw [sub_eq_add_neg, sub_eq_add_neg, resp_add, resp_neg]

def resp_div
  [GroupOps α] [GroupOps β]
  [OneHomClass F α β] [MulHomClass F α β] [InvHomClass F α β]
  [IsDivInvMonoid α] [IsDivInvMonoid β]
  (f: F) {x y: α} : f (x / y) = f x / f y := by
  rw [div_eq_mul_inv, div_eq_mul_inv, resp_mul, resp_inv]

def resp_natCast
  [AddMonoidWithOneOps α] [AddMonoidWithOneOps β]
  [ZeroHomClass F α β] [OneHomClass F α β] [AddHomClass F α β]
  [IsAddMonoidWithOne α] [IsAddMonoidWithOne β]
  (f: F) (n: Nat) : f n = n := by
  induction n with
  | zero => rw [natCast_zero, natCast_zero, resp_zero]
  | succ n ih => rw [natCast_succ, natCast_succ, resp_add, ih, resp_one]

def resp_intCast
  [AddGroupWithOneOps α] [AddGroupWithOneOps β]
  [ZeroHomClass F α β] [OneHomClass F α β] [AddHomClass F α β] [NegHomClass F α β]
  [IsAddGroupWithOne α] [IsAddGroupWithOne β]
  (f: F) (n: Int) : f n = n := by
  induction n with
  | ofNat n => rw [Int.ofNat_eq_coe, intCast_ofNat, intCast_ofNat, resp_natCast]
  | negSucc n => rw [intCast_negSucc, intCast_negSucc, resp_neg, resp_natCast]

def resp_ofNat
  [AddMonoidWithOneOps α] [AddMonoidWithOneOps β]
  [ZeroHomClass F α β] [OneHomClass F α β] [AddHomClass F α β]
  [IsAddMonoidWithOne α] [IsAddMonoidWithOne β]
  (f: F) (n: Nat) : f (OfNat.ofNat (n + 2)) = OfNat.ofNat (n + 2) := by
  rw [ofNat_eq_natCast, resp_natCast]
  symm; apply ofNat_eq_natCast

end

section

variable {α β γ: Type*}
variable [Zero α] [One α] [Add α] [Sub α] [Neg α] [Mul α] [Div α] [Inv α] [SMul ℕ α] [Pow α ℕ] [SMul ℤ α] [Pow α ℤ] [NatCast α] [IntCast α] [∀n, OfNat α (n + 2)]
variable [Zero β] [One β] [Add β] [Sub β] [Neg β] [Mul β] [Div β] [Inv β] [SMul ℕ β] [Pow β ℕ] [SMul ℤ β] [Pow β ℤ] [NatCast β] [IntCast β] [∀n, OfNat β (n + 2)]
variable [Zero γ] [One γ] [Add γ] [Sub γ] [Neg γ] [Mul γ] [Div γ] [Inv γ] [SMul ℕ γ] [Pow γ ℕ] [SMul ℤ γ] [Pow γ ℤ] [NatCast γ] [IntCast γ] [∀n, OfNat γ (n + 2)]

def AddGroupHom.comp (a: β →+ γ) (b: α →+ β) : α →+ γ where
  toFun := a.toFun ∘ b.toFun
  resp_zero := by dsimp; rw [b.resp_zero, a.resp_zero]
  resp_add { _ _ } := by dsimp; rw [b.resp_add, a.resp_add]

def GroupHom.comp (a: β →* γ) (b: α →* β) : α →* γ where
  toFun := a.toFun ∘ b.toFun
  resp_one := by dsimp; rw [b.resp_one, a.resp_one]
  resp_mul { _ _ } := by dsimp; rw [b.resp_mul, a.resp_mul]

def RingHom.comp (a: RingHom β γ) (b: RingHom α β) : RingHom α γ where
  toFun := a.toFun ∘ b.toFun
  resp_zero := by dsimp; rw [b.resp_zero, a.resp_zero]
  resp_one := by dsimp; rw [b.resp_one, a.resp_one]
  resp_add { _ _ } := by dsimp; rw [b.resp_add, a.resp_add]
  resp_mul { _ _ } := by dsimp; rw [b.resp_mul, a.resp_mul]

end

def natCast_AddGroupHom [AddMonoidWithOneOps α] [IsAddMonoidWithOne α] : ℕ →+ α where
  toFun n := n
  resp_zero := natCast_zero
  resp_add := by
    dsimp
    intro x y
    rw [natCast_add]

def intCast_AddGroupHom [AddGroupWithOneOps α] [IsAddGroupWithOne α] : ℤ →+ α where
  toFun n := n
  resp_zero := intCast_zero
  resp_add := by
    dsimp
    intro x y
    rw [intCast_add]

def AddGroupEmbedding.refl [AddMonoidOps A] : A ↪+ A where
  toEmbedding := Embedding.refl
  resp_zero := rfl
  resp_add := rfl

def GroupEmbedding.refl [MonoidOps A] : A ↪* A where
  toEmbedding := Embedding.refl
  resp_one := rfl
  resp_mul := rfl

def RingEmbedding.refl [SemiringOps A] : A ↪+* A where
  toEmbedding := Embedding.refl
  resp_zero := rfl
  resp_one := rfl
  resp_add := rfl
  resp_mul := rfl

def AddGroupEquiv.refl [AddMonoidOps A] : A ≃+ A where
  toEquiv := Equiv.refl
  resp_zero := rfl
  resp_add := rfl

def GroupEquiv.refl [MonoidOps A] : A ≃* A where
  toEquiv := Equiv.refl
  resp_one := rfl
  resp_mul := rfl

def RingEquiv.refl [SemiringOps A] : A ≃+* A where
  toEquiv := Equiv.refl
  resp_zero := rfl
  resp_one := rfl
  resp_add := rfl
  resp_mul := rfl

def AddGroupEmbedding.trans [AddMonoidOps A] [AddMonoidOps B] [AddMonoidOps C]
  (h: A ↪+ B) (g: B ↪+ C) : A ↪+ C where
  toEmbedding := h.toEmbedding.trans g.toEmbedding
  resp_zero := by
    show g.toFun (h.toFun _) = _
    rw [resp_zero, resp_zero]
  resp_add {a b} := by
    show g.toFun (h.toFun _) = _
    rw [resp_add, resp_add]
    rfl

def GroupEmbedding.trans [MonoidOps A] [MonoidOps B] [MonoidOps C]
  (h: A ↪* B) (g: B ↪* C) : A ↪* C where
  toEmbedding := h.toEmbedding.trans g.toEmbedding
  resp_one := by
    show g.toFun (h.toFun _) = _
    rw [resp_one, resp_one]
  resp_mul {a b} := by
    show g.toFun (h.toFun _) = _
    rw [resp_mul, resp_mul]
    rfl

def RingEmbedding.trans [SemiringOps A] [SemiringOps B] [SemiringOps C]
  (h: A ↪+* B) (g: B ↪+* C) : A ↪+* C where
  toEmbedding := h.toEmbedding.trans g.toEmbedding
  resp_zero := by
    show g.toFun (h.toFun _) = _
    rw [resp_zero, resp_zero]
  resp_one := by
    show g.toFun (h.toFun _) = _
    rw [resp_one, resp_one]
  resp_add {a b} := by
    show g.toFun (h.toFun _) = _
    rw [resp_add, resp_add]
    rfl
  resp_mul {a b} := by
    show g.toFun (h.toFun _) = _
    rw [resp_mul, resp_mul]
    rfl

def AddGroupEquiv.trans [AddMonoidOps A] [AddMonoidOps B] [AddMonoidOps C]
  (h: A ≃+ B) (g: B ≃+ C) : A ≃+ C where
  toEquiv := h.toEquiv.trans g.toEquiv
  resp_zero := by
    show g.toFun (h.toFun _) = _
    rw [resp_zero, resp_zero]
  resp_add {a b} := by
    show g.toFun (h.toFun _) = _
    rw [resp_add, resp_add]
    rfl

def GroupEquiv.trans [MonoidOps A] [MonoidOps B] [MonoidOps C]
  (h: A ≃* B) (g: B ≃* C) : A ≃* C where
  toEquiv := h.toEquiv.trans g.toEquiv
  resp_one := by
    show g.toFun (h.toFun _) = _
    rw [resp_one, resp_one]
  resp_mul {a b} := by
    show g.toFun (h.toFun _) = _
    rw [resp_mul, resp_mul]
    rfl

def RingEquiv.trans [SemiringOps A] [SemiringOps B] [SemiringOps C]
  (h: A ≃+* B) (g: B ≃+* C) : A ≃+* C where
  toEquiv := h.toEquiv.trans g.toEquiv
  resp_zero := by
    show g.toFun (h.toFun _) = _
    rw [resp_zero, resp_zero]
  resp_one := by
    show g.toFun (h.toFun _) = _
    rw [resp_one, resp_one]
  resp_add {a b} := by
    show g.toFun (h.toFun _) = _
    rw [resp_add, resp_add]
    rfl
  resp_mul {a b} := by
    show g.toFun (h.toFun _) = _
    rw [resp_mul, resp_mul]
    rfl

def AddGroupEquiv.symm [AddMonoidOps A] [AddMonoidOps B] (h: A ≃+ B) : B ≃+ A where
  toEquiv := h.toEquiv.symm
  resp_zero := by
    rw [←h.coe_symm 0]
    show h.toEquiv.symm 0 = h.toEquiv.symm (h.toFun 0)
    rw [h.resp_zero]
  resp_add {a b} := by
    rw [←h.coe_symm (_ + _)]
    show h.toEquiv.symm _ = h.toEquiv.symm (h.toFun _)
    erw [h.resp_add, h.rightInv, h.rightInv]

def GroupEquiv.symm [MonoidOps A] [MonoidOps B] (h: A ≃* B) : B ≃* A where
  toEquiv := h.toEquiv.symm
  resp_one := by
    rw [←h.coe_symm 1]
    show h.toEquiv.symm 1 = h.toEquiv.symm (h.toFun 1)
    rw [h.resp_one]
  resp_mul {a b} := by
    rw [←h.coe_symm (_ * _)]
    show h.toEquiv.symm _ = h.toEquiv.symm (h.toFun _)
    erw [h.resp_mul, h.rightInv, h.rightInv]

def RingEquiv.symm [SemiringOps A] [SemiringOps B] (h: A ≃+* B) : B ≃+* A where
  toEquiv := h.toEquiv.symm
  resp_zero := by
    rw [←h.coe_symm 0]
    show h.toEquiv.symm 0 = h.toEquiv.symm (h.toFun 0)
    rw [h.resp_zero]
  resp_one := by
    rw [←h.coe_symm 1]
    show h.toEquiv.symm 1 = h.toEquiv.symm (h.toFun 1)
    rw [h.resp_one]
  resp_add {a b} := by
    rw [←h.coe_symm (_ + _)]
    show h.toEquiv.symm _ = h.toEquiv.symm (h.toFun _)
    erw [h.resp_add, h.rightInv, h.rightInv]
  resp_mul {a b} := by
    rw [←h.coe_symm (_ * _)]
    show h.toEquiv.symm _ = h.toEquiv.symm (h.toFun _)
    erw [h.resp_mul, h.rightInv, h.rightInv]

def AddGroupEquiv.toEmbedding [AddMonoidOps A] [AddMonoidOps B] (h: A ≃+ B) : A ↪+ B where
  toEmbedding := h.toEquiv.toEmbedding
  resp_zero := h.resp_zero
  resp_add := h.resp_add

def GroupEquiv.toEmbedding [MonoidOps A] [MonoidOps B] (h: A ≃* B) : A ↪* B where
  toEmbedding := h.toEquiv.toEmbedding
  resp_one := h.resp_one
  resp_mul := h.resp_mul

def RingEquiv.toEmbedding [SemiringOps A] [SemiringOps B] (h: A ≃+* B) : A ↪+* B where
  toEmbedding := h.toEquiv.toEmbedding
  resp_zero := h.resp_zero
  resp_one := h.resp_one
  resp_add := h.resp_add
  resp_mul := h.resp_mul

def AddGroupEquiv.toHom [AddMonoidOps A] [AddMonoidOps B] (h: A ≃+ B) : A →+ B where
  toFun := h.toEquiv.toEmbedding
  resp_zero := h.resp_zero
  resp_add := h.resp_add

def GroupEquiv.toHom [MonoidOps A] [MonoidOps B] (h: A ≃* B) : A →* B where
  toFun := h.toEquiv.toEmbedding
  resp_one := h.resp_one
  resp_mul := h.resp_mul

def RingEquiv.toHom [SemiringOps A] [SemiringOps B] (h: A ≃+* B) : A →+* B where
  toFun := h.toEquiv.toEmbedding
  resp_zero := h.resp_zero
  resp_one := h.resp_one
  resp_add := h.resp_add
  resp_mul := h.resp_mul

def AddGroupHom.id (A: Type*) [AddMonoidOps A] : A →+ A where
  toFun := _root_.id
  resp_zero := rfl
  resp_add := rfl

def GroupHom.id (A: Type*) [MonoidOps A] : A →* A where
  toFun := _root_.id
  resp_one := rfl
  resp_mul := rfl

-- def GroupEquiv.toEmbedding [MonoidOps A] [MonoidOps B] (h: A ≃* B) : A ↪* B where
--   toEmbedding := h.toEquiv.toEmbedding
--   resp_one := h.resp_one
--   resp_mul := h.resp_mul

-- def RingEquiv.toEmbedding [SemiringOps A] [SemiringOps B] (h: A ≃+* B) : A ↪+* B where
--   toEmbedding := h.toEquiv.toEmbedding
--   resp_zero := h.resp_zero
--   resp_one := h.resp_one
--   resp_add := h.resp_add
--   resp_mul := h.resp_mul

def AddGroupEquiv.coe_symm [AddMonoidOps α] [AddMonoidOps β] (h: α ≃+ β) (x: α) :
  h.symm (h x) = x := _root_.Equiv.coe_symm _ _
def AddGroupEquiv.symm_coe [AddMonoidOps α] [AddMonoidOps β] (h: α ≃+ β) (x: β) :
  h (h.symm x) = x := _root_.Equiv.symm_coe _ _

def GroupEquiv.coe_symm [MonoidOps α] [MonoidOps β] (h: α ≃* β) (x: α) :
  h.symm (h x) = x := _root_.Equiv.coe_symm _ _
def GroupEquiv.symm_coe [MonoidOps α] [MonoidOps β] (h: α ≃* β) (x: β) :
  h (h.symm x) = x := _root_.Equiv.symm_coe _ _

def RingEquiv.coe_symm [SemiringOps α] [SemiringOps β] (h: α ≃+* β) (x: α) :
  h.symm (h x) = x := _root_.Equiv.coe_symm _ _
def RingEquiv.symm_coe [SemiringOps α] [SemiringOps β] (h: α ≃+* β) (x: β) :
  h (h.symm x) = x := _root_.Equiv.symm_coe _ _

def AddGroupEquiv.trans_symm [AddMonoidOps α] [AddMonoidOps β] (h: α ≃+ β) :
  h.trans h.symm = .refl := by
  apply DFunLike.ext
  intro x
  show h.symm (h x) = x
  rw [h.coe_symm]

def AddGroupEquiv.symm_trans [AddMonoidOps α] [AddMonoidOps β] (h: α ≃+ β) :
  h.symm.trans h = .refl := by
  apply DFunLike.ext
  intro x
  show h (h.symm x) = x
  rw [h.symm_coe]

def GroupEquiv.trans_symm [MonoidOps α] [MonoidOps β] (h: α ≃* β) :
  h.trans h.symm = .refl := by
  apply DFunLike.ext
  intro x
  show h.symm (h x) = x
  rw [h.coe_symm]

def GroupEquiv.symm_trans [MonoidOps α] [MonoidOps β] (h: α ≃* β) :
  h.symm.trans h = .refl := by
  apply DFunLike.ext
  intro x
  show h (h.symm x) = x
  rw [h.symm_coe]

def RingEquiv.trans_symm [SemiringOps α] [SemiringOps β] (h: α ≃+* β) :
  h.trans h.symm = .refl := by
  apply DFunLike.ext
  intro x
  show h.symm (h x) = x
  rw [h.coe_symm]

def RingEquiv.symm_trans [SemiringOps α] [SemiringOps β] (h: α ≃+* β) :
  h.symm.trans h = .refl := by
  apply DFunLike.ext
  intro x
  show h (h.symm x) = x
  rw [h.symm_coe]
