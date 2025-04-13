import Math.Logic.Equiv.Like
import Math.Algebra.Notation
import Math.Algebra.AddMul

section

variable (F R: Type*) (α β: outParam Type*) [FunLike F α β]
variable [Zero α] [One α] [Add α] [Mul α] [Neg α] [Inv α] [SMul R α]
variable [Zero β] [One β] [Add β] [Mul β] [Neg β] [Inv β] [SMul R β]

class IsZeroHom: Prop where
  protected map_zero: ∀f: F, f 0 = 0 := by intro f; exact f.map_zero

class IsOneHom: Prop where
  protected map_one: ∀f: F, f 1 = 1 := by intro f; exact f.map_one

class IsAddHom: Prop where
  protected map_add: ∀f: F, ∀{x y}, f (x + y) = f x + f y := by intro f; exact f.map_add

class IsMulHom: Prop where
  protected map_mul: ∀f: F, ∀{x y}, f (x * y) = f x * f y := by intro f; exact f.map_mul

class IsSMulHom: Prop where
  protected map_smul (f: F): ∀{r: R} {x: α}, f (r • x) = r • f x := by intro f; exact f.map_smul

class IsAddGroupHom: Prop extends IsZeroHom F α β, IsAddHom F α β where
class IsGroupHom: Prop extends IsOneHom F α β, IsMulHom F α β where
class IsAddGroupWithOneHom: Prop extends IsZeroHom F α β, IsOneHom F α β, IsAddHom F α β where
class IsGroupWithZeroHom: Prop extends IsZeroHom F α β, IsOneHom F α β, IsMulHom F α β where
class IsRngHom: Prop extends IsZeroHom F α β, IsAddHom F α β, IsMulHom F α β where
class IsRingHom: Prop extends IsZeroHom F α β, IsOneHom F α β, IsAddHom F α β, IsMulHom F α β where

instance (priority := 900) [IsZeroHom F α β] [IsAddHom F α β] : IsAddGroupHom F α β where
instance (priority := 900) [IsOneHom F α β ] [IsMulHom F α β] : IsGroupHom F α β where
instance (priority := 900) [IsZeroHom F α β] [IsOneHom F α β] [IsAddHom F α β] : IsAddGroupWithOneHom F α β where
instance (priority := 900) [IsZeroHom F α β] [IsOneHom F α β] [IsMulHom F α β] : IsGroupWithZeroHom F α β where
instance (priority := 900) [IsZeroHom F α β] [IsAddHom F α β] [IsMulHom F α β] : IsRngHom F α β where
instance (priority := 900) [IsZeroHom F α β] [IsOneHom F α β] [IsAddHom F α β] [IsMulHom F α β] : IsRingHom F α β where

end

section

variable (R α β: Type*)
variable [Zero α] [One α] [Add α] [Mul α] [Neg α] [Inv α] [SMul R α]
variable [Zero β] [One β] [Add β] [Mul β] [Neg β] [Inv β] [SMul R β]

structure ZeroHom where
  toFun: α -> β
  protected map_zero: toFun (0: α) = (0: β)

instance : FunLike (ZeroHom α β) α β where
instance : IsZeroHom (ZeroHom α β) α β where

structure OneHom where
  toFun: α -> β
  protected map_one: toFun (1: α) = (1: β)

instance : FunLike (OneHom α β) α β where
instance : IsOneHom (OneHom α β) α β where

structure AddHom where
  toFun: α -> β
  protected map_add: ∀{x y: α}, toFun (x + y) = toFun x + toFun y

instance : FunLike (AddHom α β) α β where
instance : IsAddHom (AddHom α β) α β where

structure MulHom where
  toFun: α -> β
  protected map_mul: ∀{x y: α}, toFun (x * y) = toFun x * toFun y

instance : FunLike (MulHom α β) α β where
instance : IsMulHom (MulHom α β) α β where

structure SMulHom (R A B: Type*) [SMul R A] [SMul R B] where
  toFun: A -> B
  protected map_smul: ∀{r: R} {x: A}, toFun (r • x) = r • toFun x

instance [SMul R A] [SMul R B] : FunLike (SMulHom R A B) A B where
instance [SMul R A] [SMul R B] : IsSMulHom (SMulHom R A B) R A B where

structure ZeroEquiv extends α ≃ β, ZeroHom α β where

instance : EquivLike (ZeroEquiv α β) α β where
instance : IsZeroHom (ZeroEquiv α β) α β where

structure OneEquiv extends α ≃ β, OneHom α β where

instance : EquivLike (OneEquiv α β) α β where
instance : IsOneHom (OneEquiv α β) α β where

structure AddEquiv extends α ≃ β, AddHom α β where

instance : EquivLike (AddEquiv α β) α β where
instance : IsAddHom (AddEquiv α β) α β where

structure MulEquiv extends α ≃ β, MulHom α β where

instance : EquivLike (MulEquiv α β) α β where
instance : IsMulHom (MulEquiv α β) α β where

structure SMulEquiv extends α ≃ β, SMulHom R α β where

instance : EquivLike (SMulEquiv R α β) α β where
instance : IsSMulHom (SMulEquiv R α β) R α β where

structure AddGroupHom extends ZeroHom α β, AddHom α β where

instance : FunLike (AddGroupHom α β) α β where
instance : IsAddGroupHom (AddGroupHom α β) α β where

structure AddGroupWithOneHom extends AddGroupHom α β, OneHom α β where

instance : FunLike (AddGroupWithOneHom α β) α β where
instance : IsAddGroupWithOneHom (AddGroupWithOneHom α β) α β where

structure GroupHom extends OneHom α β, MulHom α β where

instance : FunLike (GroupHom α β) α β where
instance : IsGroupHom (GroupHom α β) α β where

structure GroupWithZeroHom extends GroupHom α β, ZeroHom α β where

instance : FunLike (GroupWithZeroHom α β) α β where
instance : IsGroupWithZeroHom (GroupWithZeroHom α β) α β where

structure RingHom extends AddGroupWithOneHom α β, GroupWithZeroHom α β where

instance : FunLike (RingHom α β) α β where
instance : IsRingHom (RingHom α β) α β where

structure RngHom extends AddGroupHom α β, MulHom α β where

instance : FunLike (RngHom α β) α β where
instance : IsRngHom (RngHom α β) α β where

structure AddGroupEmbedding extends α ↪ β, AddGroupHom α β where

instance : EmbeddingLike (AddGroupEmbedding α β) α β where
instance : IsAddGroupHom (AddGroupEmbedding α β) α β where

structure AddGroupWithOneEmbedding extends α ↪ β, AddGroupWithOneHom α β where

instance : EmbeddingLike (AddGroupWithOneEmbedding α β) α β where
instance : IsAddGroupWithOneHom (AddGroupWithOneEmbedding α β) α β where

structure GroupEmbedding extends α ↪ β, GroupHom α β where

instance : EmbeddingLike (GroupEmbedding α β) α β where
instance : IsGroupHom (GroupEmbedding α β) α β where

structure GroupWithZeroEmbedding extends α ↪ β, GroupWithZeroHom α β where

instance : EmbeddingLike (GroupWithZeroEmbedding α β) α β where
instance : IsGroupWithZeroHom (GroupWithZeroEmbedding α β) α β where

structure RingEmbedding extends α ↪ β, RingHom α β where

instance : EmbeddingLike (RingEmbedding α β) α β where
instance : IsRingHom (RingEmbedding α β) α β where

structure RngEmbedding extends α ↪ β, RngHom α β where

instance : EmbeddingLike (RngEmbedding α β) α β where
instance : IsRngHom (RngEmbedding α β) α β where

structure AddGroupEquiv extends α ≃ β, AddGroupHom α β, ZeroEquiv α β, AddEquiv α β where

instance : EquivLike (AddGroupEquiv α β) α β where
instance : IsAddGroupHom (AddGroupEquiv α β) α β where

structure AddGroupWithOneEquiv extends α ≃ β, AddGroupWithOneHom α β, AddGroupEquiv α β, OneEquiv α β where

instance : EquivLike (AddGroupWithOneEquiv α β) α β where
instance : IsAddGroupWithOneHom (AddGroupWithOneEquiv α β) α β where

structure GroupEquiv extends α ≃ β, GroupHom α β, OneEquiv α β, MulEquiv α β where

instance : EquivLike (GroupEquiv α β) α β where
instance : IsGroupHom (GroupEquiv α β) α β where

structure GroupWithZeroEquiv extends α ≃ β, GroupWithZeroHom α β, GroupEquiv α β, ZeroEquiv α β where

instance : EquivLike (GroupWithZeroEquiv α β) α β where
instance : IsGroupWithZeroHom (GroupWithZeroEquiv α β) α β where

structure RingEquiv extends α ≃ β, RingHom α β, AddGroupEquiv α β, GroupEquiv α β where

instance : EquivLike (RingEquiv α β) α β where
instance : IsRingHom (RingEquiv α β) α β where

structure RngEquiv extends α ≃ β, RngHom α β, AddGroupEquiv α β, MulEquiv α β where

instance : EquivLike (RngEquiv α β) α β where
instance : IsRngHom (RngEquiv α β) α β where

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

variable {F R α β: Type*} [FunLike F α β]
variable [Zero α] [One α] [Add α] [Mul α] [Neg α] [Inv α] [SMul R α]
variable [Zero β] [One β] [Add β] [Mul β] [Neg β] [Inv β] [SMul R β]

def map_zero [IsZeroHom F α β] : ∀f: F, f 0 = 0 := IsZeroHom.map_zero

def map_one [IsOneHom F α β] : ∀f: F, f 1 = 1 := IsOneHom.map_one

def map_add [IsAddHom F α β] : ∀f: F, ∀{x y: α}, f (x + y) = f x + f y := IsAddHom.map_add

def map_mul [IsMulHom F α β] : ∀f: F, ∀{x y: α}, f (x * y) = f x * f y := IsMulHom.map_mul

def map_smul [IsSMulHom F R α β] (f: F): ∀{r: R} {x: α}, f (r • x) = r • f x := IsSMulHom.map_smul f

@[coe]
def toZeroHom [Zero α] [Zero β] [IsZeroHom F α β] (f: F): ZeroHom α β where
  toFun := f
  map_zero := map_zero f

@[coe]
def toOneHom [One α] [One β] [IsOneHom F α β] (f: F): OneHom α β where
  toFun := f
  map_one := map_one f

@[coe]
def toAddHom [Add α] [Add β] [IsAddHom F α β] (f: F): AddHom α β where
  toFun := f
  map_add := map_add f

@[coe]
def toMulHom [Mul α] [Mul β] [IsMulHom F α β] (f: F): MulHom α β where
  toFun := f
  map_mul := map_mul f

@[coe]
def toAddGroupHom [IsZeroHom F α β] [IsAddHom F α β] (f: F) : α →+ β where
  toFun := f
  map_zero := map_zero f
  map_add := map_add f

@[coe]
def toGroupHom [IsOneHom F α β] [IsMulHom F α β] (f: F) : α →* β where
  toFun := f
  map_one := map_one f
  map_mul := map_mul f

@[coe]
def toRingHom [IsZeroHom F α β] [IsOneHom F α β] [IsAddHom F α β] [IsMulHom F α β] (f: F) : α →+* β where
  toFun := f
  map_one := map_one f
  map_mul := map_mul f
  map_zero := map_zero f
  map_add := map_add f

end

section

variable {α β γ: Type*}
variable [Zero α] [One α] [Add α] [Mul α]
variable [Zero β] [One β] [Add β] [Mul β]
variable [Zero γ] [One γ] [Add γ] [Mul γ]

section

variable [FunLike F α β]

instance [IsZeroHom F α β] : IsOneHom F (MulOfAdd α) (MulOfAdd β) where
  map_one := map_zero (α := α) (β := β)
instance [IsOneHom F α β] : IsZeroHom F (AddOfMul α) (AddOfMul β) where
  map_zero := map_one (α := α) (β := β)

instance [IsAddHom F α β] : IsMulHom F (MulOfAdd α) (MulOfAdd β) where
  map_mul := map_add (α := α) (β := β)
instance [IsMulHom F α β] : IsAddHom F (AddOfMul α) (AddOfMul β) where
  map_add := map_mul (α := α) (β := β)

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
  map_zero := rfl

def OneHom.id (α: Type*) [One α] : OneHom α α where
  toFun := _root_.id
  map_one := rfl

def AddHom.id (α: Type*) [Add α] : AddHom α α where
  toFun := _root_.id
  map_add := rfl

def MulHom.id (α: Type*) [Mul α] : MulHom α α where
  toFun := _root_.id
  map_mul := rfl

def SMulHom.id (R α: Type*) [SMul R α] : SMulHom R α α where
  toFun := _root_.id
  map_smul := rfl

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
  map_zero := by dsimp; rw [b.map_zero, a.map_zero]

def AddHom.comp (a: AddHom β γ) (b: AddHom α β) : AddHom α γ where
  toFun := a.toFun ∘ b.toFun
  map_add { _ _ } := by dsimp; rw [b.map_add, a.map_add]

def OneHom.comp (a: OneHom β γ) (b: OneHom α β) : OneHom α γ where
  toFun := a.toFun ∘ b.toFun
  map_one := by dsimp; rw [b.map_one, a.map_one]

def MulHom.comp (a: MulHom β γ) (b: MulHom α β) : MulHom α γ where
  toFun := a.toFun ∘ b.toFun
  map_mul { _ _ } := by dsimp; rw [b.map_mul, a.map_mul]

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
  map_zero := by
    rw [←h.coe_symm 0]
    show h.toEquiv.symm 0 = h.toEquiv.symm (h.toFun 0)
    rw [h.map_zero]

def AddEquiv.symm (h: AddEquiv α β) : AddEquiv β α where
  toEquiv := h.toEquiv.symm
  map_add {a b} := by
    rw [←h.coe_symm (_ + _)]
    show h.toEquiv.symm _ = h.toEquiv.symm (h.toFun _)
    erw [h.map_add, h.rightInv, h.rightInv]

def OneEquiv.symm (h: OneEquiv α β) : OneEquiv β α where
  toEquiv := h.toEquiv.symm
  map_one := by
    rw [←h.coe_symm 1]
    show h.toEquiv.symm 1 = h.toEquiv.symm (h.toFun 1)
    rw [h.map_one]

def MulEquiv.symm (h: MulEquiv α β) : MulEquiv β α where
  toEquiv := h.toEquiv.symm
  map_mul {a b} := by
    rw [←h.coe_symm (_ * _)]
    show h.toEquiv.symm _ = h.toEquiv.symm (h.toFun _)
    erw [h.map_mul, h.rightInv, h.rightInv]

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

def AddGroupEmbedding.toHom (h: α ↪+ β) : α →+ β := h
def AddGroupWithOneEmbedding.toHom (h: α ↪+₁ β) : α →+₁ β := h
def GroupEmbedding.toHom (h: α ↪* β) : α →* β := h
def GroupWithZeroEmbedding.toHom (h: α ↪*₀ β) : α →*₀ β := h
def RingEmbedding.toHom (h: α ↪+* β) : α →+* β := h
def RngEmbedding.toHom (h: α ↪+*₀ β) : α →+*₀ β := h

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
  map_add {x y} := by
    dsimp
    show f (y.get + x.get) = _
    rw [map_add f, f_img_comm]

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
  map_mul {x y} := by
    dsimp
    show f (y.get * x.get) = _
    rw [map_mul, f_img_comm]

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

def AddGroupHom.congrAddOpp : (α →+ β) ≃ (αᵃᵒᵖ →+ βᵃᵒᵖ) where
  toFun f := {
    toFun a := .mk (f a.get)
    map_zero := map_zero f
    map_add {x y} := by
      simp
      rw [map_add, AddOpp.mk_add]
  }
  invFun f := {
    toFun a := (f (.mk a)).get
    map_zero := map_zero f
    map_add {x y} := by
      simp
      rw [map_add, AddOpp.get_add]
  }
  leftInv _ := rfl
  rightInv _ := rfl

def GroupHom.congrMulOpp : (α →* β) ≃ (αᵐᵒᵖ →* βᵐᵒᵖ) where
  toFun f := {
    toFun a := .mk (f a.get)
    map_one := map_one f
    map_mul {x y} := by
      simp
      rw [map_mul, MulOpp.mk_mul]
  }
  invFun f := {
    toFun a := (f (.mk a)).get
    map_one := map_one f
    map_mul {x y} := by
      simp
      rw [map_mul, MulOpp.get_mul]
  }
  leftInv _ := rfl
  rightInv _ := rfl

def AddGroupHom.apply_congrMulOpp (f: α →+ β) : AddGroupHom.congrAddOpp f a = .mk (f a.get) := rfl
def GroupHom.apply_congrMulOpp (f: α →* β) : GroupHom.congrMulOpp f a = .mk (f a.get) := rfl

def AddGroupHom.apply_comp (f: β →+ γ) (g: α →+ β) : (f.comp g) x = f (g x) := rfl
def GroupHom.apply_comp (f: β →* γ) (g: α →* β) : (f.comp g) x = f (g x) := rfl

@[simp] def ZeroHom.toFun_eq_coe (f: ZeroHom α β) : f.toFun = f := rfl
@[simp] def OneHom.toFun_eq_coe (f: OneHom α β) : f.toFun = f := rfl
@[simp] def AddHom.toFun_eq_coe (f: AddHom α β) : f.toFun = f := rfl
@[simp] def MulHom.toFun_eq_coe (f: MulHom α β) : f.toFun = f := rfl

@[simp] def AddMonoidHom.toFun_eq_coe (f: α →+ β) : f.toFun = f := rfl
@[simp] def MonoidHom.toFun_eq_coe (f: α →* β) : f.toFun = f := rfl
@[simp] def AddMonoidWithZeroHom.toFun_eq_coe (f: α →+₁ β) : f.toFun = f := rfl
@[simp] def MonoidWithOneHom.toFun_eq_coe (f: α →*₀ β) : f.toFun = f := rfl

variable [FunLike F α β]

instance (priority := 1100) [f: IsAddGroupWithOneHom F α β] : IsZeroHom F α β := f.toIsZeroHom
instance (priority := 1100) [f: IsAddGroupWithOneHom F α β] : IsOneHom F α β := f.toIsOneHom
instance (priority := 1100) [f: IsAddGroupWithOneHom F α β] : IsAddHom F α β := f.toIsAddHom

instance (priority := 1100) [f: IsGroupWithZeroHom F α β] : IsZeroHom F α β := f.toIsZeroHom
instance (priority := 1100) [f: IsGroupWithZeroHom F α β] : IsOneHom F α β := f.toIsOneHom
instance (priority := 1100) [f: IsGroupWithZeroHom F α β] : IsMulHom F α β := f.toIsMulHom

instance (priority := 1100) [f: IsRngHom F α β] : IsZeroHom F α β := f.toIsZeroHom
instance (priority := 1100) [f: IsRngHom F α β] : IsAddHom F α β := f.toIsAddHom
instance (priority := 1100) [f: IsRngHom F α β] : IsMulHom F α β := f.toIsMulHom

instance (priority := 1100) [f: IsRingHom F α β] : IsZeroHom F α β := f.toIsZeroHom
instance (priority := 1100) [f: IsRingHom F α β] : IsOneHom F α β := f.toIsOneHom
instance (priority := 1100) [f: IsRingHom F α β] : IsAddHom F α β := f.toIsAddHom
instance (priority := 1100) [f: IsRingHom F α β] : IsMulHom F α β := f.toIsMulHom
