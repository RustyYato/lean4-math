import Math.Logic.Equiv.Basic
import Math.Algebra.Notation
import Math.Algebra.AddMul

section

variable (α β: Type*)
variable [Zero α] [One α] [Add α] [Mul α] [Neg α] [Inv α]
variable [Zero β] [One β] [Add β] [Mul β] [Neg β] [Inv β]

class IsZeroHom (F: Type*) (α β: outParam Type*) [Zero α] [Zero β] [FunLike F α β]: Prop where
    resp_zero: ∀f: F, f 0 = 0

def resp_zero {F α β: Type*} [Zero α] [Zero β] [FunLike F α β] [IsZeroHom F α β] : ∀f: F, f 0 = 0 := IsZeroHom.resp_zero

class IsOneHom (F: Type*) (α β: outParam Type*) [One α] [One β] [FunLike F α β]: Prop where
    resp_one: ∀f: F, f 1 = 1

def resp_one {F α β: Type*} [One α] [One β] [FunLike F α β] [IsOneHom F α β] : ∀f: F, f 1 = 1 := IsOneHom.resp_one

class IsAddHom (F: Type*) (α β: outParam Type*) [Add α] [Add β] [FunLike F α β]: Prop where
    resp_add: ∀f: F, ∀{x y}, f (x + y) = f x + f y

def resp_add {F α β: Type*} [Add α] [Add β] [FunLike F α β] [IsAddHom F α β] : ∀f: F, ∀{x y: α}, f (x + y) = f x + f y := IsAddHom.resp_add

class IsMulHom (F: Type*) (α β: outParam Type*) [Mul α] [Mul β] [FunLike F α β]: Prop where
    resp_mul: ∀f: F, ∀{x y}, f (x * y) = f x * f y

def resp_mul {F α β: Type*} [Mul α] [Mul β] [FunLike F α β] [IsMulHom F α β] : ∀f: F, ∀{x y: α}, f (x * y) = f x * f y := IsMulHom.resp_mul

class IsSMulHom (F R: Type*) (A B: outParam Type*) [FunLike F A B] [SMul R A] [SMul R B]: Prop where
  resp_smul (f: F): ∀{r: R} {x: A}, f (r • x) = r • f x

def resp_smul
  [FunLike F A B] [SMul R A] [SMul R B]
  [IsSMulHom F R A B]
  (f: F): ∀{r: R} {x: A}, f (r • x) = r • f x := IsSMulHom.resp_smul f

structure ZeroHom where
  toFun: α -> β
  resp_zero: toFun (0: α) = (0: β)

instance : FunLike (ZeroHom α β) α β where
  coe := ZeroHom.toFun
  coe_inj := by
    intro ⟨_, _⟩ ⟨_, _⟩ _
    congr

instance : IsZeroHom (ZeroHom α β) α β := ⟨ZeroHom.resp_zero⟩

structure OneHom where
  toFun: α -> β
  resp_one: toFun (1: α) = (1: β)

instance : FunLike (OneHom α β) α β where
  coe := OneHom.toFun
  coe_inj := by
    intro ⟨_, _⟩ ⟨_, _⟩ _
    congr

instance : IsOneHom (OneHom α β) α β := ⟨OneHom.resp_one⟩

structure AddHom where
  toFun: α -> β
  resp_add: ∀{x y: α}, toFun (x + y) = toFun x + toFun y

instance : FunLike (AddHom α β) α β where
  coe := AddHom.toFun
  coe_inj := by
    intro ⟨_, _⟩ ⟨_, _⟩ _
    congr

instance : IsAddHom (AddHom α β) α β := ⟨AddHom.resp_add⟩

structure MulHom where
  toFun: α -> β
  resp_mul: ∀{x y: α}, toFun (x * y) = toFun x * toFun y

instance : FunLike (MulHom α β) α β where
  coe := MulHom.toFun
  coe_inj := by
    intro ⟨_, _⟩ ⟨_, _⟩ _
    congr

instance : IsMulHom (MulHom α β) α β := ⟨MulHom.resp_mul⟩

structure ZeroEquiv extends α ≃ β, ZeroHom α β where

instance : FunLike (ZeroEquiv α β) α β where
  coe f := f.toFun
  coe_inj := by
    intro f g _; repeat obtain ⟨f, _⟩ := f
    congr 1
    apply DFunLike.coe_inj
    assumption

instance : IsZeroHom (ZeroEquiv α β) α β := ⟨ZeroEquiv.resp_zero⟩

structure OneEquiv extends α ≃ β, OneHom α β where

instance : FunLike (OneEquiv α β) α β where
  coe f := f.toFun
  coe_inj := by
    intro f g _; repeat obtain ⟨f, _⟩ := f
    congr 1
    apply DFunLike.coe_inj
    assumption

instance : IsOneHom (OneEquiv α β) α β := ⟨OneEquiv.resp_one⟩

structure AddEquiv extends α ≃ β, AddHom α β where

instance : FunLike (AddEquiv α β) α β where
  coe f := f.toFun
  coe_inj := by
    intro f g _; repeat obtain ⟨f, _⟩ := f
    congr 1
    apply DFunLike.coe_inj
    assumption

instance : IsAddHom (AddEquiv α β) α β := ⟨AddEquiv.resp_add⟩

structure MulEquiv extends α ≃ β, MulHom α β where

instance : FunLike (MulEquiv α β) α β where
  coe f := f.toFun
  coe_inj := by
    intro f g _; repeat obtain ⟨f, _⟩ := f
    congr 1
    apply DFunLike.coe_inj
    assumption

instance : IsMulHom (MulEquiv α β) α β := ⟨MulEquiv.resp_mul⟩

structure SMulHom (R A B: Type*) [SMul R A] [SMul R B] where
  toFun: A -> B
  resp_smul: ∀{r: R} {x: A}, toFun (r • x) = r • toFun x

instance [SMul R A] [SMul R B] : FunLike (SMulHom R A B) A B where
  coe := SMulHom.toFun
  coe_inj := by
    intro f g eq; cases f; congr

instance [SMul R A] [SMul R B] : IsSMulHom (SMulHom R A B) R A B where
  resp_smul := SMulHom.resp_smul

structure AddGroupHom extends ZeroHom α β, AddHom α β where

instance : FunLike (AddGroupHom α β) α β where
  coe f := f.toFun
  coe_inj := by
    intro f g _; repeat obtain ⟨f, _⟩ := f
    congr

instance : IsZeroHom (AddGroupHom α β) α β where
  resp_zero f := f.resp_zero

instance : IsAddHom (AddGroupHom α β) α β where
  resp_add f := f.resp_add

structure AddGroupWithOneHom extends AddGroupHom α β, OneHom α β where

instance : FunLike (AddGroupWithOneHom α β) α β where
  coe f := f.toFun
  coe_inj := by
    intro f g _; repeat obtain ⟨f, _⟩ := f
    congr

instance : IsZeroHom (AddGroupWithOneHom α β) α β where
  resp_zero f := f.resp_zero

instance : IsOneHom (AddGroupWithOneHom α β) α β where
  resp_one f := f.resp_one

instance : IsAddHom (AddGroupWithOneHom α β) α β where
  resp_add f := f.resp_add

structure GroupHom extends OneHom α β, MulHom α β where

instance : FunLike (GroupHom α β) α β where
  coe f := f.toFun
  coe_inj := by
    intro f g _; repeat obtain ⟨f, _⟩ := f
    congr

instance : IsOneHom (GroupHom α β) α β where
  resp_one f := f.resp_one

instance : IsMulHom (GroupHom α β) α β where
  resp_mul f := f.resp_mul

structure GroupWithZeroHom extends GroupHom α β, ZeroHom α β where

instance : FunLike (GroupWithZeroHom α β) α β where
  coe f := f.toFun
  coe_inj := by
    intro f g _; repeat obtain ⟨f, _⟩ := f
    congr

instance : IsZeroHom (GroupWithZeroHom α β) α β where
  resp_zero f := f.resp_zero

instance : IsOneHom (GroupWithZeroHom α β) α β where
  resp_one f := f.resp_one

instance : IsMulHom (GroupWithZeroHom α β) α β where
  resp_mul f := f.resp_mul

structure RingHom extends AddGroupWithOneHom α β, GroupWithZeroHom α β where

instance : FunLike (RingHom α β) α β where
  coe f := f.toFun
  coe_inj := by
    intro f g _; repeat obtain ⟨f, _⟩ := f
    congr

instance : IsZeroHom (RingHom α β) α β where
  resp_zero f := f.resp_zero

instance : IsAddHom (RingHom α β) α β where
  resp_add f := f.resp_add

instance : IsOneHom (RingHom α β) α β where
  resp_one f := f.resp_one

instance : IsMulHom (RingHom α β) α β where
  resp_mul f := f.resp_mul

structure RngHom extends AddGroupHom α β, MulHom α β where

instance : FunLike (RngHom α β) α β where
  coe f := f.toFun
  coe_inj := by
    intro f g _; repeat obtain ⟨f, _⟩ := f
    congr

instance : IsZeroHom (RngHom α β) α β where
  resp_zero f := f.resp_zero

instance : IsAddHom (RngHom α β) α β where
  resp_add f := f.resp_add

instance : IsMulHom (RngHom α β) α β where
  resp_mul f := f.resp_mul

structure AddGroupEmbedding extends α ↪ β, AddGroupHom α β where

instance : FunLike (AddGroupEmbedding α β) α β where
  coe f := f.toFun
  coe_inj := by
    intro f g _; repeat obtain ⟨f, _⟩ := f
    congr

instance : IsZeroHom (AddGroupEmbedding α β) α β where
  resp_zero f := f.resp_zero

instance : IsAddHom (AddGroupEmbedding α β) α β where
  resp_add f := f.resp_add

structure AddGroupWithOneEmbedding extends α ↪ β, AddGroupWithOneHom α β where

instance : FunLike (AddGroupWithOneEmbedding α β) α β where
  coe f := f.toFun
  coe_inj := by
    intro f g _; repeat obtain ⟨f, _⟩ := f
    congr

instance : IsZeroHom (AddGroupWithOneEmbedding α β) α β where
  resp_zero f := f.resp_zero

instance : IsOneHom (AddGroupWithOneEmbedding α β) α β where
  resp_one f := f.resp_one

instance : IsAddHom (AddGroupWithOneEmbedding α β) α β where
  resp_add f := f.resp_add

structure GroupEmbedding extends α ↪ β, GroupHom α β where

instance : FunLike (GroupEmbedding α β) α β where
  coe f := f.toFun
  coe_inj := by
    intro f g _; repeat obtain ⟨f, _⟩ := f
    congr

instance : IsOneHom (GroupEmbedding α β) α β where
  resp_one f := f.resp_one

instance : IsMulHom (GroupEmbedding α β) α β where
  resp_mul f := f.resp_mul

structure GroupWithZeroEmbedding extends α ↪ β, GroupWithZeroHom α β where

instance : FunLike (GroupWithZeroEmbedding α β) α β where
  coe f := f.toFun
  coe_inj := by
    intro f g _; repeat obtain ⟨f, _⟩ := f
    congr

instance : IsZeroHom (GroupWithZeroEmbedding α β) α β where
  resp_zero f := f.resp_zero

instance : IsOneHom (GroupWithZeroEmbedding α β) α β where
  resp_one f := f.resp_one

instance : IsMulHom (GroupWithZeroEmbedding α β) α β where
  resp_mul f := f.resp_mul

structure RingEmbedding extends α ↪ β, RingHom α β where

instance : FunLike (RingEmbedding α β) α β where
  coe f := f.toFun
  coe_inj := by
    intro f g _; repeat obtain ⟨f, _⟩ := f
    congr

instance : IsZeroHom (RingEmbedding α β) α β where
  resp_zero f := f.resp_zero

instance : IsAddHom (RingEmbedding α β) α β where
  resp_add f := f.resp_add

instance : IsOneHom (RingEmbedding α β) α β where
  resp_one f := f.resp_one

instance : IsMulHom (RingEmbedding α β) α β where
  resp_mul f := f.resp_mul

structure RngEmbedding extends α ↪ β, RngHom α β where

instance : FunLike (RngEmbedding α β) α β where
  coe f := f.toFun
  coe_inj := by
    intro f g _; repeat obtain ⟨f, _⟩ := f
    congr

instance : IsZeroHom (RngEmbedding α β) α β where
  resp_zero f := f.resp_zero

instance : IsAddHom (RngEmbedding α β) α β where
  resp_add f := f.resp_add

instance : IsMulHom (RngEmbedding α β) α β where
  resp_mul f := f.resp_mul

structure AddGroupEquiv extends α ≃ β, AddGroupHom α β, ZeroEquiv α β, AddEquiv α β where

instance : FunLike (AddGroupEquiv α β) α β where
  coe f := f.toFun
  coe_inj := by
    intro f g _; repeat obtain ⟨f, _⟩ := f
    congr 1
    apply DFunLike.coe_inj
    assumption

instance : IsZeroHom (AddGroupEquiv α β) α β where
  resp_zero f := f.resp_zero

instance : IsAddHom (AddGroupEquiv α β) α β where
  resp_add f := f.resp_add

structure AddGroupWithOneEquiv extends α ≃ β, AddGroupWithOneHom α β, AddGroupEquiv α β, OneEquiv α β where

instance : FunLike (AddGroupWithOneEquiv α β) α β where
  coe f := f.toFun
  coe_inj := by
    intro f g _; repeat obtain ⟨f, _⟩ := f
    congr 1
    apply DFunLike.coe_inj
    assumption

instance : IsZeroHom (AddGroupWithOneEquiv α β) α β where
  resp_zero f := f.resp_zero

instance : IsOneHom (AddGroupWithOneEquiv α β) α β where
  resp_one f := f.resp_one

instance : IsAddHom (AddGroupWithOneEquiv α β) α β where
  resp_add f := f.resp_add

structure GroupEquiv extends α ≃ β, GroupHom α β, OneEquiv α β, MulEquiv α β where

instance : FunLike (GroupEquiv α β) α β where
  coe f := f.toFun
  coe_inj := by
    intro f g _; repeat obtain ⟨f, _⟩ := f
    congr 1
    apply DFunLike.coe_inj
    assumption

instance : IsOneHom (GroupEquiv α β) α β where
  resp_one f := f.resp_one

instance : IsMulHom (GroupEquiv α β) α β where
  resp_mul f := f.resp_mul

structure GroupWithZeroEquiv extends α ≃ β, GroupWithZeroHom α β, GroupEquiv α β, ZeroEquiv α β where

instance : FunLike (GroupWithZeroEquiv α β) α β where
  coe f := f.toFun
  coe_inj := by
    intro f g _; repeat obtain ⟨f, _⟩ := f
    congr 1
    apply DFunLike.coe_inj
    assumption

instance : IsZeroHom (GroupWithZeroEquiv α β) α β where
  resp_zero f := f.resp_zero

instance : IsOneHom (GroupWithZeroEquiv α β) α β where
  resp_one f := f.resp_one

instance : IsMulHom (GroupWithZeroEquiv α β) α β where
  resp_mul f := f.resp_mul

structure RingEquiv extends α ≃ β, RingHom α β, AddGroupEquiv α β, GroupEquiv α β where

instance : FunLike (RingEquiv α β) α β where
  coe f := f.toFun
  coe_inj := by
    intro f g _; repeat obtain ⟨f, _⟩ := f
    congr 1
    apply DFunLike.coe_inj
    assumption

instance : IsZeroHom (RingEquiv α β) α β where
  resp_zero f := f.resp_zero

instance : IsAddHom (RingEquiv α β) α β where
  resp_add f := f.resp_add

instance : IsOneHom (RingEquiv α β) α β where
  resp_one f := f.resp_one

instance : IsMulHom (RingEquiv α β) α β where
  resp_mul f := f.resp_mul

structure RngEquiv extends α ≃ β, RngHom α β, AddGroupEquiv α β, MulEquiv α β where

instance : FunLike (RngEquiv α β) α β where
  coe f := f.toFun
  coe_inj := by
    intro f g _; repeat obtain ⟨f, _⟩ := f
    congr 1
    apply DFunLike.coe_inj
    assumption

instance : IsZeroHom (RngEquiv α β) α β where
  resp_zero f := f.resp_zero

instance : IsAddHom (RngEquiv α β) α β where
  resp_add f := f.resp_add

instance : IsMulHom (RngEquiv α β) α β where
  resp_mul f := f.resp_mul

infixr:25 " →+ " => AddGroupHom
infixr:25 " →+₁ " => AddGroupWithOneHom
infixr:25 " →* " => GroupHom
infixr:25 " →*₀ " => GroupWithZeroHom

infixr:25 " →+* " => RingHom
infixr:25 " →+*₀ " => RngHom

infixr:25 " ↪+ " => AddGroupEmbedding
infixr:25 " ↪+₁ " => AddGroupWithOneEmbedding
infixr:25 " ↪* " => GroupEmbedding
infixr:25 " ↪*₀ " => GroupWithZeroEmbedding

infixr:25 " ↪+* " => RingEmbedding
infixr:25 " ↪+*₀ " => RngEmbedding

infixr:25 " ≃+ " => AddGroupEquiv
infixr:25 " ≃+₁ " => AddGroupWithOneEquiv
infixr:25 " ≃* " => GroupEquiv
infixr:25 " ≃*₀ " => GroupWithZeroEquiv

infixr:25 " ≃+* " => RingEquiv
infixr:25 " ≃+*₀ " => RngEquiv

end

section

variable {F α β: Type*} [FunLike F α β]
variable [Zero α] [One α] [Add α] [Mul α] [Neg α] [Inv α]
variable [Zero β] [One β] [Add β] [Mul β] [Neg β] [Inv β]

@[coe]
def toZeroHom [Zero α] [Zero β] [IsZeroHom F α β] (f: F): ZeroHom α β where
  toFun := f
  resp_zero := resp_zero f

@[coe]
def toOneHom [One α] [One β] [IsOneHom F α β] (f: F): OneHom α β where
  toFun := f
  resp_one := resp_one f

@[coe]
def toAddHom [Add α] [Add β] [IsAddHom F α β] (f: F): AddHom α β where
  toFun := f
  resp_add := resp_add f

@[coe]
def toMulHom [Mul α] [Mul β] [IsMulHom F α β] (f: F): MulHom α β where
  toFun := f
  resp_mul := resp_mul f

@[coe]
def toAddGroupHom [IsZeroHom F α β] [IsAddHom F α β] (f: F) : α →+ β where
  toFun := f
  resp_zero := resp_zero f
  resp_add := resp_add f

@[coe]
def toGroupHom [IsOneHom F α β] [IsMulHom F α β] (f: F) : α →* β where
  toFun := f
  resp_one := resp_one f
  resp_mul := resp_mul f

@[coe]
def toRingHom [IsZeroHom F α β] [IsOneHom F α β] [IsAddHom F α β] [IsMulHom F α β] (f: F) : α →+* β where
  toFun := f
  resp_one := resp_one f
  resp_mul := resp_mul f
  resp_zero := resp_zero f
  resp_add := resp_add f

end

section

variable {α β γ: Type*}
variable [Zero α] [One α] [Add α] [Mul α]
variable [Zero β] [One β] [Add β] [Mul β]
variable [Zero γ] [One γ] [Add γ] [Mul γ]

section

variable [FunLike F α β]

instance [IsZeroHom F α β] : IsOneHom F (MulOfAdd α) (MulOfAdd β) where
  resp_one := resp_zero (α := α) (β := β)
instance [IsOneHom F α β] : IsZeroHom F (AddOfMul α) (AddOfMul β) where
  resp_zero := resp_one (α := α) (β := β)

instance [IsAddHom F α β] : IsMulHom F (MulOfAdd α) (MulOfAdd β) where
  resp_mul := resp_add (α := α) (β := β)
instance [IsMulHom F α β] : IsAddHom F (AddOfMul α) (AddOfMul β) where
  resp_add := resp_mul (α := α) (β := β)

end

instance : Coe (α ↪+ β) (α →+ β) where
  coe h := { h with }
instance : Coe (α ≃+ β) (α ↪+ β) where
  coe h := { h.toEmbedding, h with }
instance : Coe (α ↪+₁ β) (α →+₁ β) where
  coe h := { h with }
instance : Coe (α ≃+₁ β) (α ↪+₁ β) where
  coe h := { h.toEmbedding, h with }
instance : Coe (α ↪* β) (α →* β) where
  coe h := { h with }
instance : Coe (α ≃* β) (α ↪* β) where
  coe h := { h.toEmbedding, h with }
instance : Coe (α ↪*₀ β) (α →*₀ β) where
  coe h := { h with }
instance : Coe (α ≃*₀ β) (α ↪*₀ β) where
  coe h := { h.toEmbedding, h with }
instance : Coe (α ↪+*₀ β) (α →+*₀ β) where
  coe h := { h with }
instance : Coe (α ≃+*₀ β) (α ↪+*₀ β) where
  coe h := { h.toEmbedding, h with }
instance : Coe (α ↪+* β) (α →+* β) where
  coe h := { h with }
instance : Coe (α ≃+* β) (α ↪+* β) where
  coe h := { h.toEmbedding, h with }
instance : Coe (α →+* β) (α →+ β) where
  coe h := { h with }
instance : Coe (α ↪+* β) (α ↪+ β) where
  coe h := { h with }
instance : Coe (α ≃+* β) (α ≃+ β) where
  coe h := { h with }
instance : Coe (α →+* β) (α →* β) where
  coe h := { h with }
instance : Coe (α ↪+* β) (α ↪* β) where
  coe h := { h with }
instance : Coe (α ≃+* β) (α ≃* β) where
  coe h := { h with }
instance : Coe (α →+ β) (ZeroHom α β) where
  coe h := { h with }
instance : Coe (α →+ β) (AddHom α β) where
  coe h := { h with }
instance : Coe (α →* β) (OneHom α β) where
  coe h := { h with }
instance : Coe (α →* β) (MulHom α β) where
  coe h := { h with }
instance : Coe (α →+₁ β) (OneHom α β) where
  coe h := { h with }
instance : Coe (α →*₀ β) (ZeroHom α β) where
  coe h := { h with }

def ZeroHom.id (α: Type*) [Zero α] : ZeroHom α α where
  toFun := _root_.id
  resp_zero := rfl

def OneHom.id (α: Type*) [One α] : OneHom α α where
  toFun := _root_.id
  resp_one := rfl

def AddHom.id (α: Type*) [Add α] : AddHom α α where
  toFun := _root_.id
  resp_add := rfl

def MulHom.id (α: Type*) [Mul α] : MulHom α α where
  toFun := _root_.id
  resp_mul := rfl

def AddGroupHom.id (α: Type*) [Zero α] [Add α] : α →+ α := {
  AddHom.id _, ZeroHom.id _ with
}

def AddGroupWithOneHom.id (α: Type*) [Zero α] [One α] [Add α] : α →+₁ α := {
  AddGroupHom.id _, OneHom.id _ with
}

def GroupHom.id (α: Type*) [One α] [Mul α] : α →* α := {
  MulHom.id _, OneHom.id _ with
}

def GroupWithZeroHom.id (α: Type*) [Zero α] [One α] [Mul α] : α →*₀ α := {
  GroupHom.id _, ZeroHom.id _ with
}

def RngHom.id (α: Type*) [Zero α] [Add α] [Mul α] : α →+*₀ α := {
  MulHom.id _, AddGroupHom.id _ with
}

def RingHom.id (α: Type*) [Zero α] [One α] [Add α] [Mul α] : α →+* α := {
  GroupHom.id _, AddGroupHom.id _ with
}

def ZeroHom.comp (a: ZeroHom β γ) (b: ZeroHom α β) : ZeroHom α γ where
  toFun := a.toFun ∘ b.toFun
  resp_zero := by dsimp; rw [b.resp_zero, a.resp_zero]

def AddHom.comp (a: AddHom β γ) (b: AddHom α β) : AddHom α γ where
  toFun := a.toFun ∘ b.toFun
  resp_add { _ _ } := by dsimp; rw [b.resp_add, a.resp_add]

def OneHom.comp (a: OneHom β γ) (b: OneHom α β) : OneHom α γ where
  toFun := a.toFun ∘ b.toFun
  resp_one := by dsimp; rw [b.resp_one, a.resp_one]

def MulHom.comp (a: MulHom β γ) (b: MulHom α β) : MulHom α γ where
  toFun := a.toFun ∘ b.toFun
  resp_mul { _ _ } := by dsimp; rw [b.resp_mul, a.resp_mul]

def AddGroupHom.comp (a: β →+ γ) (b: α →+ β) : α →+ γ := {
  a.toAddHom.comp b.toAddHom, a.toZeroHom.comp b.toZeroHom with
}

def AddGroupWithOneHom.comp (a: β →+₁ γ) (b: α →+₁ β) : α →+₁ γ := {
  a.toAddGroupHom.comp b.toAddGroupHom, a.toOneHom.comp b.toOneHom with
}

def GroupHom.comp (a: β →* γ) (b: α →* β) : α →* γ := {
  a.toMulHom.comp b.toMulHom, a.toOneHom.comp b.toOneHom with
}

def GroupWithZeroHom.comp (a: β →*₀ γ) (b: α →*₀ β) : α →*₀ γ := {
  a.toGroupHom.comp b.toGroupHom, a.toZeroHom.comp b.toZeroHom with
}

def RngHom.comp (a: β →+*₀ γ) (b: α →+*₀ β) : α →+*₀ γ := {
  a.toMulHom.comp b.toMulHom, a.toAddGroupHom.comp b.toAddGroupHom with
}

def RingHom.comp (a: β →+* γ) (b: α →+* β) : α →+* γ := {
  a.toGroupHom.comp b.toGroupHom, a.toAddGroupHom.comp b.toAddGroupHom with
}

def AddGroupEmbedding.refl : α ↪+ α := {
  Embedding.rfl, AddGroupHom.id _ with
}

def AddGroupWithOneEmbedding.refl : α ↪+₁ α := {
  Embedding.rfl, AddGroupWithOneHom.id _ with
}

def GroupEmbedding.refl : α ↪* α := {
  Embedding.rfl, GroupHom.id _ with
}

def GroupWithZeroEmbedding.refl : α ↪*₀ α := {
  Embedding.rfl, GroupWithZeroHom.id _ with
}

def RngEmbedding.refl : α ↪+*₀ α := {
  Embedding.rfl, RngHom.id _ with
}

def RingEmbedding.refl : α ↪+* α := {
  Embedding.rfl, RingHom.id _ with
}

def AddGroupEquiv.refl : α ≃+ α := {
  Equiv.rfl, AddGroupHom.id _ with
}

def AddGroupWithOneEquiv.refl : α ≃+₁ α := {
  Equiv.rfl, AddGroupWithOneHom.id _ with
}

def GroupEquiv.refl : α ≃* α := {
  Equiv.rfl, GroupHom.id _ with
}

def GroupWithZeroEquiv.refl : α ≃*₀ α := {
  Equiv.rfl, GroupWithZeroHom.id _ with
}

def RngEquiv.refl : α ≃+*₀ α := {
  Equiv.rfl, RngHom.id _ with
}

def RingEquiv.refl : α ≃+* α := {
  Equiv.rfl, RingHom.id _ with
}

def AddGroupEmbedding.trans (h: α ↪+ β) (g: β ↪+ γ) : α ↪+ γ := {
  h.toEmbedding.trans g.toEmbedding, g.toAddGroupHom.comp h.toAddGroupHom with
}

def AddGroupWithOneEmbedding.trans (h: α ↪+₁ β) (g: β ↪+₁ γ) : α ↪+₁ γ := {
  h.toEmbedding.trans g.toEmbedding, g.toAddGroupWithOneHom.comp h.toAddGroupWithOneHom with
}

def GroupEmbedding.trans (h: α ↪* β) (g: β ↪* γ) : α ↪* γ := {
  h.toEmbedding.trans g.toEmbedding, g.toGroupHom.comp h.toGroupHom with
}

def GroupWithZeroEmbedding.trans (h: α ↪*₀ β) (g: β ↪*₀ γ) : α ↪*₀ γ := {
  h.toEmbedding.trans g.toEmbedding, g.toGroupWithZeroHom.comp h.toGroupWithZeroHom with
}

def RngEmbedding.trans (h: α ↪+*₀ β) (g: β ↪+*₀ γ) : α ↪+*₀ γ := {
  h.toEmbedding.trans g.toEmbedding, g.toRngHom.comp h.toRngHom with
}

def RingEmbedding.trans (h: α ↪+* β) (g: β ↪+* γ) : α ↪+* γ := {
  h.toEmbedding.trans g.toEmbedding, g.toRingHom.comp h.toRingHom with
}

def AddGroupEquiv.trans (h: α ≃+ β) (g: β ≃+ γ) : α ≃+ γ := {
  h.toEquiv.trans g.toEquiv, g.toAddGroupHom.comp h.toAddGroupHom with
}

def AddGroupWithOneEquiv.trans (h: α ≃+₁ β) (g: β ≃+₁ γ) : α ≃+₁ γ := {
  h.toEquiv.trans g.toEquiv, g.toAddGroupWithOneHom.comp h.toAddGroupWithOneHom with
}

def GroupEquiv.trans (h: α ≃* β) (g: β ≃* γ) : α ≃* γ := {
  h.toEquiv.trans g.toEquiv, g.toGroupHom.comp h.toGroupHom with
}

def GroupWithZeroEquiv.trans (h: α ≃*₀ β) (g: β ≃*₀ γ) : α ≃*₀ γ := {
  h.toEquiv.trans g.toEquiv, g.toGroupWithZeroHom.comp h.toGroupWithZeroHom with
}

def RngEquiv.trans (h: α ≃+*₀ β) (g: β ≃+*₀ γ) : α ≃+*₀ γ := {
  h.toEquiv.trans g.toEquiv, g.toRngHom.comp h.toRngHom with
}

def RingEquiv.trans (h: α ≃+* β) (g: β ≃+* γ) : α ≃+* γ := {
  h.toEquiv.trans g.toEquiv, g.toRingHom.comp h.toRingHom with
}

def ZeroEquiv.symm (h: ZeroEquiv α β) : ZeroEquiv β α where
  toEquiv := h.toEquiv.symm
  resp_zero := by
    rw [←h.coe_symm 0]
    show h.toEquiv.symm 0 = h.toEquiv.symm (h.toFun 0)
    rw [h.resp_zero]

def AddEquiv.symm (h: AddEquiv α β) : AddEquiv β α where
  toEquiv := h.toEquiv.symm
  resp_add {a b} := by
    rw [←h.coe_symm (_ + _)]
    show h.toEquiv.symm _ = h.toEquiv.symm (h.toFun _)
    erw [h.resp_add, h.rightInv, h.rightInv]

def OneEquiv.symm (h: OneEquiv α β) : OneEquiv β α where
  toEquiv := h.toEquiv.symm
  resp_one := by
    rw [←h.coe_symm 1]
    show h.toEquiv.symm 1 = h.toEquiv.symm (h.toFun 1)
    rw [h.resp_one]

def MulEquiv.symm (h: MulEquiv α β) : MulEquiv β α where
  toEquiv := h.toEquiv.symm
  resp_mul {a b} := by
    rw [←h.coe_symm (_ * _)]
    show h.toEquiv.symm _ = h.toEquiv.symm (h.toFun _)
    erw [h.resp_mul, h.rightInv, h.rightInv]

def AddGroupEquiv.symm (h: α ≃+ β) : β ≃+ α := {
  h.toAddEquiv.symm, h.toZeroEquiv.symm with
}

def AddGroupWithOneEquiv.symm (h: α ≃+₁ β) : β ≃+₁ α := {
  h.toAddGroupEquiv.symm, h.toOneEquiv.symm with
}

def GroupEquiv.symm (h: α ≃* β) : β ≃* α := {
  h.toMulEquiv.symm, h.toOneEquiv.symm with
}

def GroupWithZeroEquiv.symm (h: α ≃*₀ β) : β ≃*₀ α := {
  h.toGroupEquiv.symm, h.toZeroEquiv.symm with
}

def RngEquiv.symm (h: α ≃+*₀ β) : β ≃+*₀ α := {
  h.toAddGroupEquiv.symm,  h.toMulEquiv.symm with
}

def RingEquiv.symm (h: α ≃+* β) : β ≃+* α := {
  h.toAddGroupEquiv.symm,  h.toGroupEquiv.symm with
}

def AddGroupEquiv.toEmbedding (h: α ≃+ β) : α ↪+ β := h
def AddGroupWithOneEquiv.toEmbedding (h: α ≃+₁ β) : α ↪+₁ β := h
def GroupEquiv.toEmbedding (h: α ≃* β) : α ↪* β := h
def GroupWithZeroEquiv.toEmbedding (h: α ≃*₀ β) : α ↪*₀ β := h
def RingEquiv.toEmbedding (h: α ≃+* β) : α ↪+* β := h
def RngEquiv.toEmbedding (h: α ≃+*₀ β) : α ↪+*₀ β := h
def AddGroupEquiv.toHom (h: α ≃+ β) : α →+ β := h
def AddGroupWithOneEquiv.toHom (h: α ≃+₁ β) : α →+₁ β := h
def GroupEquiv.toHom (h: α ≃* β) : α →* β := h
def GroupWithZeroEquiv.toHom (h: α ≃*₀ β) : α →*₀ β := h
def RingEquiv.toHom (h: α ≃+* β) : α →+* β := h
def RngEquiv.toHom (h: α ≃+*₀ β) : α →+*₀ β := h

def AddGroupEquiv.coe_symm (h: α ≃+ β) (x: α) :
  h.symm (h x) = x := _root_.Equiv.coe_symm _ _
def AddGroupEquiv.symm_coe (h: α ≃+ β) (x: β) :
  h (h.symm x) = x := _root_.Equiv.symm_coe _ _

def AddGroupWithOneEquiv.coe_symm (h: α ≃+₁ β) (x: α) :
  h.symm (h x) = x := _root_.Equiv.coe_symm _ _
def AddGroupWithOneEquiv.symm_coe (h: α ≃+₁ β) (x: β) :
  h (h.symm x) = x := _root_.Equiv.symm_coe _ _

def GroupEquiv.coe_symm (h: α ≃* β) (x: α) :
  h.symm (h x) = x := _root_.Equiv.coe_symm _ _
def GroupEquiv.symm_coe (h: α ≃* β) (x: β) :
  h (h.symm x) = x := _root_.Equiv.symm_coe _ _

def GroupWithZeroEquiv.coe_symm (h: α ≃*₀ β) (x: α) :
  h.symm (h x) = x := _root_.Equiv.coe_symm _ _
def GroupWithZeroEquiv.symm_coe (h: α ≃*₀ β) (x: β) :
  h (h.symm x) = x := _root_.Equiv.symm_coe _ _

def RingEquiv.coe_symm (h: α ≃+* β) (x: α) :
  h.symm (h x) = x := _root_.Equiv.coe_symm _ _
def RingEquiv.symm_coe (h: α ≃+* β) (x: β) :
  h (h.symm x) = x := _root_.Equiv.symm_coe _ _

def RngEquiv.coe_symm (h: α ≃+*₀ β) (x: α) :
  h.symm (h x) = x := _root_.Equiv.coe_symm _ _
def RngEquiv.symm_coe (h: α ≃+*₀ β) (x: β) :
  h (h.symm x) = x := _root_.Equiv.symm_coe _ _

syntax "hom_equiv_trans_symm_impl" ident : tactic
macro_rules
| `(tactic|hom_equiv_trans_symm_impl $e) => `(tactic|apply DFunLike.ext; first|apply ($e).coe_symm|(apply ($e).symm_coe))

def AddGroupEquiv.trans_symm (h: α ≃+ β) :
  h.trans h.symm = .refl := by hom_equiv_trans_symm_impl h

def AddGroupEquiv.symm_trans (h: α ≃+ β) :
  h.symm.trans h = .refl := by hom_equiv_trans_symm_impl h

def AddGroupWithOneEquiv.trans_symm (h: α ≃+₁ β) :
  h.trans h.symm = .refl := by hom_equiv_trans_symm_impl h

def AddGroupWithOneEquiv.symm_trans (h: α ≃+₁ β) :
  h.symm.trans h = .refl := by hom_equiv_trans_symm_impl h

def GroupEquiv.trans_symm (h: α ≃* β) :
  h.trans h.symm = .refl := by hom_equiv_trans_symm_impl h

def GroupEquiv.symm_trans (h: α ≃* β) :
  h.symm.trans h = .refl := by hom_equiv_trans_symm_impl h

def GroupWithZeroEquiv.trans_symm (h: α ≃*₀ β) :
  h.trans h.symm = .refl := by hom_equiv_trans_symm_impl h

def GroupWithZeroEquiv.symm_trans (h: α ≃*₀ β) :
  h.symm.trans h = .refl := by hom_equiv_trans_symm_impl h

def RingEquiv.trans_symm (h: α ≃+* β) :
  h.trans h.symm = .refl := by hom_equiv_trans_symm_impl h

def RingEquiv.symm_trans (h: α ≃+* β) :
  h.symm.trans h = .refl := by hom_equiv_trans_symm_impl h

def RngEquiv.symm_trans (h: α ≃+*₀ β) :
  h.symm.trans h = .refl := by hom_equiv_trans_symm_impl h

def AddHom.toAddOpp (f: AddHom α β) (f_img_comm: ∀a b, f a + f b = f b + f a) : AddHom αᵃᵒᵖ β where
  toFun x := f x.get
  resp_add {x y} := by
    dsimp
    show f (y.get + x.get) = _
    rw [_root_.resp_add, f_img_comm]

def AddGroupHom.toAddOpp (f: α →+ β) (f_img_comm: ∀a b, f a + f b = f b + f a) : αᵃᵒᵖ →+ β := {
  f.toZeroHom, f.toAddHom.toAddOpp f_img_comm with
}

def AddGroupWithOneHom.toAddOpp (f: α →+₁ β) (f_img_comm: ∀a b, f a + f b = f b + f a) : αᵃᵒᵖ →+₁ β := {
  f.toZeroHom, f.toOneHom, f.toAddHom.toAddOpp f_img_comm with
}

def RingHom.toAddOpp (f: α →+* β) (f_img_comm: ∀a b, f a + f b = f b + f a) : αᵃᵒᵖ →+* β := {
  f.toGroupHom, f.toAddGroupHom.toAddOpp f_img_comm with
}

def MulHom.toMulOpp (f: MulHom α β) (f_img_comm: ∀a b, f a * f b = f b * f a) : MulHom αᵐᵒᵖ β where
  toFun x := f x.get
  resp_mul {x y} := by
    dsimp
    show f (y.get * x.get) = _
    rw [_root_.resp_mul, f_img_comm]

def GroupHom.toMulOpp (f: α →* β) (f_img_comm: ∀a b, f a * f b = f b * f a) : αᵐᵒᵖ →* β := {
  f.toOneHom, f.toMulHom.toMulOpp f_img_comm with
}

def GroupWithZeroHom.toMulOpp (f: α →*₀ β) (f_img_comm: ∀a b, f a * f b = f b * f a) : αᵐᵒᵖ →*₀ β := {
  f.toZeroHom, f.toOneHom, f.toMulHom.toMulOpp f_img_comm with
}

def RingHom.toMulOpp (f: α →+* β) (f_img_comm: ∀a b, f a * f b = f b * f a) : αᵐᵒᵖ →+* β := {
  f.toAddGroupHom, f.toGroupHom.toMulOpp f_img_comm with
}

def AddGroupEmbedding.inj (h: α ↪+ β) : Function.Injective h := Embedding.inj h.toEmbedding
def AddGroupWithOneEmbedding.inj (h: α ↪+₁ β) : Function.Injective h := Embedding.inj h.toEmbedding
def GroupEmbedding.inj (h: α ↪* β) : Function.Injective h := Embedding.inj h.toEmbedding
def GroupWithZeroEmbedding.inj (h: α ↪*₀ β) : Function.Injective h := Embedding.inj h.toEmbedding
def RingEmbedding.inj (h: α ↪+* β) : Function.Injective h := Embedding.inj h.toEmbedding

def AddGroupEquiv.inj (h: α ≃+ β) : Function.Injective h := Equiv.inj h.toEquiv
def AddGroupWithOneEquiv.inj (h: α ≃+₁ β) : Function.Injective h := Equiv.inj h.toEquiv
def GroupEquiv.inj (h: α ≃* β) : Function.Injective h := Equiv.inj h.toEquiv
def GroupWithZeroEquiv.inj (h: α ≃*₀ β) : Function.Injective h := Equiv.inj h.toEquiv
def RingEquiv.inj (h: α ≃+* β) : Function.Injective h := Equiv.inj h.toEquiv
def RngEquiv.inj (h: α ≃+*₀ β) : Function.Injective h := Equiv.inj h.toEquiv

@[ext] def AddGroupHom.ext (f g: α →+ β) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _
@[ext] def AddGroupWithOneHom.ext (f g: α →+₁ β) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _
@[ext] def GroupHom.ext (f g: α →* β) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _
@[ext] def GroupWithZeroHom.ext (f g: α →*₀ β) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _
@[ext] def RingHom.ext (f g: α →+* β) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _

@[ext] def AddGroupEmbedding.ext (f g: α ↪+ β) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _
@[ext] def AddGroupWithOneEmbedding.ext (f g: α ↪+₁ β) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _
@[ext] def GroupEmbedding.ext (f g: α ↪* β) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _
@[ext] def GroupWithZeroEmbedding.ext (f g: α ↪*₀ β) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _
@[ext] def RingEmbedding.ext (f g: α ↪+* β) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _

@[ext] def AddGroupEquiv.ext (f g: α ≃+ β) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _
@[ext] def AddGroupWithOneEquiv.ext (f g: α ≃+₁ β) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _
@[ext] def GroupEquiv.ext (f g: α ≃* β) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _
@[ext] def GroupWithZeroEquiv.ext (f g: α ≃*₀ β) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _
@[ext] def RingEquiv.ext (f g: α ≃+* β) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _
