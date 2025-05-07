import Math.Logic.Equiv.Like
import Math.Algebra.Notation
import Math.Algebra.AddMul

section

variable (F R: Type*) (α β: outParam Type*) [FunLike F α β]
variable [Zero α] [One α] [Add α] [Mul α] [SMul R α]
variable [Zero β] [One β] [Add β] [Mul β] [SMul R β]
variable [Zero R] [One R] [Add R] [Mul R]

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

class IsAddMulHom: Prop where
  protected map_add_to_mul: ∀f: F, ∀{x y}, f (x + y) = f x * f y := by intro f; exact f.map_add_to_mul

class IsMulAddHom: Prop where
  protected map_mul_to_add: ∀f: F, ∀{x y}, f (x * y) = f x + f y := by intro f; exact f.map_mul_to_add

class IsZeroOneHom: Prop where
  protected map_zero_to_one: ∀f: F, f 0 = 1 := by intro f; exact f.map_zero_to_one

class IsOneZeroHom: Prop where
  protected map_one_to_zero: ∀f: F, f 1 = 0 := by intro f; exact f.map_one_to_zero

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
variable [Zero α] [One α] [Add α] [Mul α] [SMul R α]
variable [Zero β] [One β] [Add β] [Mul β] [SMul R β]
variable [Zero R] [One R] [Add R] [Mul R]

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

structure AddMulHom (A B: Type*) [Add A] [Mul B] where
  toFun: A -> B
  protected map_add_to_mul: ∀{a b: A}, toFun (a + b) = toFun a * toFun b

instance : FunLike (AddMulHom α β) α β where
instance : IsAddMulHom (AddMulHom α β) α β where

structure MulAddHom (A B: Type*) [Mul A] [Add B] where
  toFun: A -> B
  protected map_mul_to_add: ∀{a b: A}, toFun (a * b) = toFun a + toFun b

instance : FunLike (MulAddHom α β) α β where
instance : IsMulAddHom (MulAddHom α β) α β where

structure ZeroOneHom (A B: Type*) [Zero A] [One B] where
  toFun: A -> B
  protected map_zero_to_one: toFun 0 = 1

instance : FunLike (ZeroOneHom α β) α β where
instance : IsZeroOneHom (ZeroOneHom α β) α β where

structure OneZeroHom (A B: Type*) [One A] [Zero B] where
  toFun: A -> B
  protected map_one_to_zero: toFun 1 = 0

instance : FunLike (OneZeroHom α β) α β where
instance : IsOneZeroHom (OneZeroHom α β) α β where

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

structure AddMulEquiv extends α ≃ β, AddMulHom α β where

instance : EquivLike (AddMulEquiv α β) α β where
instance : IsAddMulHom (AddMulEquiv α β) α β where

structure MulAddEquiv extends α ≃ β, MulAddHom α β where

instance : EquivLike (MulAddEquiv α β) α β where
instance : IsMulAddHom (MulAddEquiv α β) α β where

structure ZeroOneEquiv extends α ≃ β, ZeroOneHom α β where

instance : EquivLike (ZeroOneEquiv α β) α β where
instance : IsZeroOneHom (ZeroOneEquiv α β) α β where

structure OneZeroEquiv extends α ≃ β, OneZeroHom α β where

instance : EquivLike (OneZeroEquiv α β) α β where
instance : IsOneZeroHom (OneZeroEquiv α β) α β where

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

structure LinearMap extends AddHom α β, SMulHom R α β where

instance : FunLike (LinearMap R α β) α β where
instance : IsAddHom (LinearMap R α β) α β where
instance : IsSMulHom (LinearMap R α β) R α β where

structure ExpHom extends AddMulHom α β, ZeroOneHom α β where

instance : FunLike (ExpHom α β) α β where
instance : IsAddMulHom (ExpHom α β) α β where
instance : IsZeroOneHom (ExpHom α β) α β where

structure LogHom extends MulAddHom α β, OneZeroHom α β where

instance : FunLike (LogHom α β) α β where
instance : IsMulAddHom (LogHom α β) α β where
instance : IsOneZeroHom (LogHom α β) α β where

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

structure LinearEmbedding extends α ↪ β, LinearMap R α β where

instance : EmbeddingLike (LinearEmbedding R α β) α β where
instance : IsAddHom (LinearEmbedding R α β) α β where
instance : IsSMulHom (LinearEmbedding R α β) R α β where

structure ExpEmbedding extends α ↪ β, ExpHom α β where

instance : EmbeddingLike (ExpEmbedding α β) α β where
instance : IsAddMulHom (ExpEmbedding α β) α β where
instance : IsZeroOneHom (ExpEmbedding α β) α β where

structure LogEmbedding extends α ↪ β, LogHom α β where

instance : EmbeddingLike (LogEmbedding α β) α β where
instance : IsMulAddHom (LogEmbedding α β) α β where
instance : IsOneZeroHom (LogEmbedding α β) α β where

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
instance : IsMulHom (RingEquiv α β) α β where

structure RngEquiv extends α ≃ β, RngHom α β, AddGroupEquiv α β, MulEquiv α β where

instance : EquivLike (RngEquiv α β) α β where
instance : IsRngHom (RngEquiv α β) α β where

structure LinearEquiv extends α ≃ β, LinearMap R α β, AddEquiv α β, SMulEquiv R α β where

instance : EquivLike (LinearEquiv R α β) α β where
instance : IsAddHom (LinearEquiv R α β) α β where
instance : IsSMulHom (LinearEquiv R α β) R α β where

structure ExpEquiv extends α ≃ β, ExpHom α β, AddMulEquiv α β, ZeroOneEquiv α β where

instance : EquivLike (ExpEquiv α β) α β where
instance : IsAddMulHom (ExpEquiv α β) α β where
instance : IsZeroOneHom (ExpEquiv α β) α β where

structure LogEquiv extends α ≃ β, LogHom α β, MulAddEquiv α β, OneZeroEquiv α β where

instance : EquivLike (LogEquiv α β) α β where
instance : IsMulAddHom (LogEquiv α β) α β where
instance : IsOneZeroHom (LogEquiv α β) α β where

class AlgebraMap extends RingHom α β where

def algebraMap
  {R α: Type*}
  [Zero R] [One R] [Add R] [Mul R]
  [Zero α] [One α] [Add α] [Mul α]
  [AlgebraMap R α] : RingHom R α := AlgebraMap.toRingHom

class IsAlgebraMapHom
  (F R: Type*)
  (α β: outParam Type*)
  [FunLike F α β]
  [Zero R] [One R] [Add R] [Mul R]
  [Zero α] [One α] [Add α] [Mul α] [AlgebraMap R α]
  [Zero β] [One β] [Add β] [Mul β] [AlgebraMap R β]: Prop where
  protected map_algebraMap (f: F): ∀(r: R), f (algebraMap r) = algebraMap r := by intro f; exact f.map_algebraMap

variable [AlgebraMap R α] [AlgebraMap R β]

def IsAlgebraMapHom.toZeroHom
  (F R: Type*)
  (α β: outParam Type*)
  [FunLike F α β]
  [Zero R] [One R] [Add R] [Mul R]
  [Zero α] [One α] [Add α] [Mul α] [AlgebraMap R α]
  [Zero β] [One β] [Add β] [Mul β] [AlgebraMap R β]
  [IsAlgebraMapHom F R α β]
  : IsZeroHom F α β where
  map_zero f := by
    rw [←IsZeroHom.map_zero (algebraMap (R := R)), IsAlgebraMapHom.map_algebraMap f,
      IsZeroHom.map_zero (algebraMap (R := R))]

def IsAlgebraMapHom.toOneHom
  (F R: Type*)
  (α β: outParam Type*)
  [FunLike F α β]
  [Zero R] [One R] [Add R] [Mul R]
  [Zero α] [One α] [Add α] [Mul α] [AlgebraMap R α]
  [Zero β] [One β] [Add β] [Mul β] [AlgebraMap R β]
  [IsAlgebraMapHom F R α β] : IsOneHom F α β where
  map_one f := by
    rw [←IsOneHom.map_one (algebraMap (R := R)), IsAlgebraMapHom.map_algebraMap f,
      IsOneHom.map_one (algebraMap (R := R))]

structure AlgebraMapHom where
  toFun: α -> β
  protected map_algebraMap: ∀(r: R), toFun (algebraMap r) = algebraMap r

instance : FunLike (AlgebraMapHom R α β) α β where
instance : IsAlgebraMapHom (AlgebraMapHom R α β) R α β where

structure AlgebraMapEquiv extends α ≃ β, AlgebraMapHom R α β where

instance : EquivLike (AlgebraMapEquiv R α β) α β where
instance : IsAlgebraMapHom (AlgebraMapEquiv R α β) R α β where

structure AlgHom extends AddHom α β, MulHom α β, AlgebraMapHom R α β where

instance : FunLike (AlgHom R α β) α β where
instance : IsAlgebraMapHom (AlgHom R α β) R α β where
instance : IsRingHom (AlgHom R α β) α β := {
  IsAlgebraMapHom.toZeroHom (AlgHom R α β) R α β,
  IsAlgebraMapHom.toOneHom (AlgHom R α β) R α β with
}

structure AlgEmbedding extends α ↪ β, AlgHom R α β where

instance : EmbeddingLike (AlgEmbedding R α β) α β where
instance : IsAlgebraMapHom (AlgEmbedding R α β) R α β where
instance : IsRingHom (AlgEmbedding R α β) α β where
  map_zero f := IsZeroHom.map_zero f.toAlgHom
  map_one f := IsOneHom.map_one f.toAlgHom

structure AlgEquiv extends α ≃ β, AddEquiv α β, MulEquiv α β, AlgebraMapEquiv R α β, AlgHom R α β where

instance : EquivLike (AlgEquiv R α β) α β where
instance : IsAlgebraMapHom (AlgEquiv R α β) R α β where
instance : IsRingHom (AlgEquiv R α β) α β where
  map_zero f := IsZeroHom.map_zero f.toAlgHom
  map_one f := IsOneHom.map_one f.toAlgHom

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

notation:25 A " →ₗ[" R "] " B => LinearMap R A B
notation:25 A " ↪ₗ[" R "] " B => LinearEmbedding R A B
notation:25 A " ≃ₗ[" R "] " B => LinearEquiv R A B

notation:25 A " →ₐ[" R "] " B => AlgHom R A B
notation:25 A " ↪ₐ[" R "] " B => AlgEmbedding R A B
notation:25 A " ≃ₐ[" R "] " B => AlgEquiv R A B

infixr:25 " →ₙₐ* " => AddMulHom
infixr:25 " ≃ₙₐ* " => AddMulEquiv
infixr:25 " →ₙₘ+ " => MulAddHom
infixr:25 " ≃ₙₘ+ " => MulAddEquiv

infixr:25 " →₀₁ " => ZeroOneHom
infixr:25 " ≃₀₁ " => ZeroOneEquiv
infixr:25 " →₁₀ " => OneZeroHom
infixr:25 " ≃₁₀ " => OneZeroEquiv

infixr:25 " →ₐ* " => ExpHom
infixr:25 " ↪ₐ* " => ExpEmbedding
infixr:25 " ≃ₐ* " => ExpEquiv
infixr:25 " →ₘ+ " => LogHom
infixr:25 " ↪ₘ+ " => LogEmbedding
infixr:25 " ≃ₘ+ " => LogEquiv

end

section

variable {F R α β: Type*} [FunLike F α β]
variable [Zero R] [One R] [Add R] [Mul R]
variable [Zero α] [One α] [Add α] [Mul α] [SMul R α] [AlgebraMap R α]
variable [Zero β] [One β] [Add β] [Mul β] [SMul R β] [AlgebraMap R β]

def map_zero [IsZeroHom F α β] : ∀f: F, f 0 = 0 := IsZeroHom.map_zero

def map_one [IsOneHom F α β] : ∀f: F, f 1 = 1 := IsOneHom.map_one

def map_add [IsAddHom F α β] : ∀f: F, ∀{x y: α}, f (x + y) = f x + f y := IsAddHom.map_add

def map_mul [IsMulHom F α β] : ∀f: F, ∀{x y: α}, f (x * y) = f x * f y := IsMulHom.map_mul

def map_smul [IsSMulHom F R α β] (f: F): ∀{r: R} {x: α}, f (r • x) = r • f x := IsSMulHom.map_smul f

def map_zero_to_one [IsZeroOneHom F α β] (f: F) : f 0 = 1 := IsZeroOneHom.map_zero_to_one _

def map_one_to_zero [IsOneZeroHom F α β] (f: F) : f 1 = 0 := IsOneZeroHom.map_one_to_zero _

def map_add_to_mul [IsAddMulHom F α β] (f: F): ∀{a b: α}, f (a + b) = f a * f b := IsAddMulHom.map_add_to_mul f

def map_mul_to_add [IsMulAddHom F α β] (f: F): ∀{a b: α}, f (a * b) = f a + f b := IsMulAddHom.map_mul_to_add f

def map_algebraMap [IsAlgebraMapHom F R α β] (f: F): ∀(r: R), f (algebraMap r) = algebraMap r := IsAlgebraMapHom.map_algebraMap f

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

@[coe]
def toLinearMap
  [FunLike F A B] [SMul R A] [SMul R B] [Add A] [Add B]
  [IsAddHom F A B] [IsSMulHom F R A B] (f: F) : LinearMap R A B where
  toFun := f
  map_add := map_add _
  map_smul := map_smul _

end

section

variable {R α β γ δ: Type*}
variable [Zero R] [One R] [Add R] [Mul R]
variable [Zero α] [One α] [Add α] [Mul α] [SMul R α] [AlgebraMap R α]
variable [Zero β] [One β] [Add β] [Mul β] [SMul R β] [AlgebraMap R β]
variable [Zero γ] [One γ] [Add γ] [Mul γ] [SMul R γ] [AlgebraMap R γ]
variable [Zero δ] [One δ] [Add δ] [Mul δ] [SMul R δ] [AlgebraMap R δ]

section

variable [FunLike F α β]

-- reduce priority of these conversions since they are def-eq to the originals
-- and that leads to bad type-class synth and timeouts.

instance (priority := 500) [IsZeroHom F α β] : IsOneHom F (MulOfAdd α) (MulOfAdd β) where
  map_one := map_zero (α := α) (β := β)
instance (priority := 500) [IsOneHom F α β] : IsZeroHom F (AddOfMul α) (AddOfMul β) where
  map_zero := map_one (α := α) (β := β)

instance (priority := 500) [IsAddHom F α β] : IsMulHom F (MulOfAdd α) (MulOfAdd β) where
  map_mul := map_add (α := α) (β := β)
instance (priority := 500) [IsMulHom F α β] : IsAddHom F (AddOfMul α) (AddOfMul β) where
  map_add := map_mul (α := α) (β := β)

instance (priority := 500) [IsZeroOneHom F α β] : IsOneHom F (MulOfAdd α) β where
  map_one := map_zero_to_one (α := α) (β := β)

instance (priority := 500) [IsZeroOneHom F α β] : IsZeroHom F α (AddOfMul β) where
  map_zero := map_zero_to_one (α := α) (β := β)

instance (priority := 500) [IsOneZeroHom F α β] : IsOneHom F α (MulOfAdd β) where
  map_one := map_one_to_zero (α := α) (β := β)

instance (priority := 500) [IsOneZeroHom F α β] : IsZeroHom F (AddOfMul α) β where
  map_zero := map_one_to_zero (α := α) (β := β)

instance (priority := 500) [IsAddMulHom F α β] : IsMulHom F (MulOfAdd α) β where
  map_mul := map_add_to_mul (α := α) (β := β)

instance (priority := 500) [IsAddMulHom F α β] : IsAddHom F α (AddOfMul β) where
  map_add := map_add_to_mul (α := α) (β := β)

instance (priority := 500) [IsMulAddHom F α β] : IsMulHom F α (MulOfAdd β) where
  map_mul := map_mul_to_add (α := α) (β := β)

instance (priority := 500) [IsMulAddHom F α β] : IsAddHom F (AddOfMul α) β where
  map_add := map_mul_to_add (α := α) (β := β)

end

attribute [local irreducible] AddOfMul MulOfAdd

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
instance : Coe (α ↪ₗ[R] β) (α →ₗ[R] β) where
  coe h := { h with }
instance : Coe (α ≃ₗ[R] β) (α ↪ₗ[R] β) where
  coe h := { h.toEmbedding, h with }
instance : Coe (α ↪ₐ[R] β) (α →ₐ[R] β) where
  coe h := { h with }
instance : Coe (α ≃ₐ[R] β) (α ↪ₐ[R] β) where
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
instance : Coe (α →ₗ[R] β) (SMulHom R α β) where
  coe h := { h with }
instance : Coe (α ↪ₐ* β) (α →ₐ* β) where
  coe h := { h with }
instance : Coe (α ≃ₐ* β) (α ↪ₐ* β) where
  coe h := { h, h.toEmbedding with }
instance : Coe (α ↪ₘ+ β) (α →ₘ+ β) where
  coe h := { h with }
instance : Coe (α ≃ₘ+ β) (α ↪ₘ+ β) where
  coe h := { h, h.toEmbedding with }

def ZeroHom.copy (f: ZeroHom α β) (g: α -> β) (h: f = g) : ZeroHom α β where
  toFun := g
  map_zero := h ▸ map_zero f

def OneHom.copy (f: OneHom α β) (g: α -> β) (h: f = g) : OneHom α β where
  toFun := g
  map_one := h ▸ map_one f

def AddHom.copy (f: AddHom α β) (g: α -> β) (h: f = g) : AddHom α β where
  toFun := g
  map_add := h ▸ map_add f

def MulHom.copy (f: MulHom α β) (g: α -> β) (h: f = g) : MulHom α β where
  toFun := g
  map_mul := h ▸ map_mul f

def SMulHom.copy (f: SMulHom R α β) (g: α -> β) (h: f = g) : SMulHom R α β where
  toFun := g
  map_smul := h ▸ map_smul f

def ZeroOneHom.copy (f: α →₀₁ β) (g: α -> β) (h: f = g) : α →₀₁ β where
  toFun := g
  map_zero_to_one := h ▸ map_zero_to_one f

def OneZeroHom.copy (f: α →₁₀ β) (g: α -> β) (h: f = g) : α →₁₀ β where
  toFun := g
  map_one_to_zero := h ▸ map_one_to_zero f

def AddMulHom.copy (f: α →ₙₐ* β) (g: α -> β) (h: f = g) : α →ₙₐ* β where
  toFun := g
  map_add_to_mul := h ▸ map_add_to_mul f

def MulAddHom.copy (f: α →ₙₘ+ β) (g: α -> β) (h: f = g) : α →ₙₘ+ β where
  toFun := g
  map_mul_to_add := h ▸ map_mul_to_add f

def AlgebraMapHom.copy (f: AlgebraMapHom R α β) (g: α -> β) (h: f = g) : AlgebraMapHom R α β where
  toFun := g
  map_algebraMap := h ▸ map_algebraMap f

def AddGroupHom.copy (f: α →+ β) (g: α -> β) (h: f = g) : α →+ β := {
  f.toZeroHom.copy g h, f.toAddHom.copy g h with
}

def AddGroupWithOneHom.copy (f: α →+₁ β) (g: α -> β) (h: f = g) : α →+₁ β := {
  f.toZeroHom.copy g h, f.toOneHom.copy g h, f.toAddHom.copy g h with
}

def GroupHom.copy (f: α →* β) (g: α -> β) (h: f = g) : α →* β := {
  f.toOneHom.copy g h, f.toMulHom.copy g h with
}

def GroupWithZeroHom.copy (f: α →*₀ β) (g: α -> β) (h: f = g) : α →*₀ β := {
  f.toZeroHom.copy g h, f.toOneHom.copy g h, f.toMulHom.copy g h with
}

def RngHom.copy (f: α →+*₀ β) (g: α -> β) (h: f = g) : α →+*₀ β := {
  f.toZeroHom.copy g h, f.toAddHom.copy g h, f.toMulHom.copy g h with
}

def RingHom.copy (f: α →+* β) (g: α -> β) (h: f = g) : α →+* β := {
  f.toZeroHom.copy g h, f.toOneHom.copy g h, f.toAddHom.copy g h, f.toMulHom.copy g h with
}

def LinearMap.copy (f: α →ₗ[R] β) (g: α -> β) (h: f = g) : α →ₗ[R] β := {
  f.toAddHom.copy g h, f.toSMulHom.copy g h with
}

def AlgHom.copy (f: α →ₐ[R] β) (g: α -> β) (h: f = g) : α →ₐ[R] β := {
  f.toAddHom.copy g h, f.toMulHom.copy g h, f.toAlgebraMapHom.copy g h with
}

def ExpHom.copy (f: α →ₐ* β) (g: α -> β) (h: f = g) : α →ₐ* β := {
  f.toZeroOneHom.copy g h, f.toAddMulHom.copy g h with
}

def LogHom.copy (f: α →ₘ+ β) (g: α -> β) (h: f = g) : α →ₘ+ β := {
  f.toOneZeroHom.copy g h, f.toMulAddHom.copy g h with
}

def AddGroupWithOneEmbedding.copy (f: α ↪+₁ β) (g: α -> β) (h: f = g) : α ↪+₁ β := {
  f.toEmbedding.copy g h, f.toAddGroupWithOneHom.copy g h with
}

def GroupEmbedding.copy (f: α ↪* β) (g: α -> β) (h: f = g) : α ↪* β := {
  f.toEmbedding.copy g h, f.toGroupHom.copy g h with
}

def GroupWithZeroEmbedding.copy (f: α ↪*₀ β) (g: α -> β) (h: f = g) : α ↪*₀ β := {
  f.toEmbedding.copy g h, f.toGroupWithZeroHom.copy g h with
}

def RngEmbedding.copy (f: α ↪+*₀ β) (g: α -> β) (h: f = g) : α ↪+*₀ β := {
  f.toEmbedding.copy g h, f.toRngHom.copy g h with
}

def RingEmbedding.copy (f: α ↪+* β) (g: α -> β) (h: f = g) : α ↪+* β := {
  f.toEmbedding.copy g h, f.toRingHom.copy g h with
}

def LinearEmbedding.copy (f: α ↪ₗ[R] β) (g: α -> β) (h: f = g) : α ↪ₗ[R] β := {
  f.toEmbedding.copy g h, f.toLinearMap.copy g h with
}

def AlgEmbedding.copy (f: α ↪ₐ[R] β) (g: α -> β) (h: f = g) : α ↪ₐ[R] β := {
  f.toEmbedding.copy g h, f.toAlgHom.copy g h with
}

def ExpEmbedding.copy (f: α ↪ₐ* β ) (g: α -> β) (h: f = g) : α ↪ₐ* β := {
  f.toEmbedding.copy g h, f.toExpHom.copy g h with
}

def LogEmbedding.copy (f: α ↪ₘ+ β) (g: α -> β) (h: f = g) : α ↪ₘ+ β := {
  f.toEmbedding.copy g h, f.toLogHom.copy g h with
}

protected def ZeroHom.id (α: Type*) [Zero α] : ZeroHom α α where
  toFun := id
  map_zero := rfl

protected def OneHom.id (α: Type*) [One α] : OneHom α α where
  toFun := id
  map_one := rfl

protected def AddHom.id (α: Type*) [Add α] : AddHom α α where
  toFun := id
  map_add := rfl

protected def MulHom.id (α: Type*) [Mul α] : MulHom α α where
  toFun := id
  map_mul := rfl

protected def SMulHom.id (R α: Type*) [SMul R α] : SMulHom R α α where
  toFun := id
  map_smul := rfl

protected def AlgebraMapHom.id (R α: Type*)
  [Zero R] [One R] [Add R] [Mul R]
  [Zero α] [One α] [Add α] [Mul α]
  [AlgebraMap R α] : AlgebraMapHom R α α where
  toFun := id
  map_algebraMap _ := rfl

protected def AddGroupHom.id (α: Type*) [Zero α] [Add α] : α →+ α := {
  AddHom.id _, ZeroHom.id _ with
}

protected def AddGroupWithOneHom.id (α: Type*) [Zero α] [One α] [Add α] : α →+₁ α := {
  AddGroupHom.id _, OneHom.id _ with
}

protected def GroupHom.id (α: Type*) [One α] [Mul α] : α →* α := {
  MulHom.id _, OneHom.id _ with
}

protected def GroupWithZeroHom.id (α: Type*) [Zero α] [One α] [Mul α] : α →*₀ α := {
  GroupHom.id _, ZeroHom.id _ with
}

protected def RngHom.id (α: Type*) [Zero α] [Add α] [Mul α] : α →+*₀ α := {
  MulHom.id _, AddGroupHom.id _ with
}

protected def RingHom.id (α: Type*) [Zero α] [One α] [Add α] [Mul α] : α →+* α := {
  GroupHom.id _, AddGroupHom.id _ with
}

protected def LinearMap.id (α: Type*) [Add α] [SMul R α] : α →ₗ[R] α := {
  AddHom.id _, SMulHom.id _ _ with
}

protected def AlgHom.id (α: Type*)
  [Zero α] [One α] [Add α] [Mul α]
  [AlgebraMap R α] : α →ₐ[R] α := {
  AddHom.id _, MulHom.id _, AlgebraMapHom.id _ _ with
}

@[simp] def AddGroupHom.apply_id : AddGroupHom.id α x = x := rfl
@[simp] def AddGroupWithOneHom.apply_id : AddGroupWithOneHom.id α x = x := rfl
@[simp] def GroupHom.apply_id : GroupHom.id α x = x := rfl
@[simp] def GroupWithZeroHom.apply_id : GroupWithZeroHom.id α x = x := rfl
@[simp] def RngHom.apply_id : RngHom.id α x = x := rfl
@[simp] def RingHom.apply_id : RingHom.id α x = x := rfl
@[simp] def LinearMap.apply_id : LinearMap.id (R := R) α x = x := rfl
@[simp] def AlgHom.apply_id : AlgHom.id (R := R) α x = x := rfl

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

def SMulHom.comp (a: SMulHom R β γ) (b: SMulHom R α β) : SMulHom R α γ where
  toFun := a.toFun ∘ b.toFun
  map_smul { _ _ } := by dsimp; rw [b.map_smul, a.map_smul]

def AlgebraMapHom.comp (a: AlgebraMapHom R β γ) (b: AlgebraMapHom R α β) : AlgebraMapHom R α γ where
  toFun := a.toFun ∘ b.toFun
  map_algebraMap { _ } := by dsimp; rw [b.map_algebraMap, a.map_algebraMap]

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

def LinearMap.comp (a: β →ₗ[R] γ) (b: α →ₗ[R] β) : α →ₗ[R] γ := {
  a.toAddHom.comp b.toAddHom, a.toSMulHom.comp b.toSMulHom with
}

def AlgHom.comp (a: β →ₐ[R] γ) (b: α →ₐ[R] β) : α →ₐ[R] γ := {
  a.toAddHom.comp b.toAddHom, a.toMulHom.comp b.toMulHom,
    a.toAlgebraMapHom.comp b.toAlgebraMapHom with
}

def ZeroOneHom.zero_comp [FunLike F α β] [IsZeroHom F α β] (g: β →₀₁ γ) (f: F) : α →₀₁ γ where
  toFun := g ∘ f
  map_zero_to_one := by dsimp; rw [map_zero, map_zero_to_one]

def ZeroOneHom.comp_one [FunLike F β γ] [IsOneHom F β γ] (g: F) (f: α →₀₁ β) : α →₀₁ γ where
  toFun := g ∘ f
  map_zero_to_one := by dsimp; rw [map_zero_to_one, map_one]

def OneZeroHom.one_comp [FunLike F α β] [IsOneHom F α β] (g: β →₁₀ γ) (f: F) : α →₁₀ γ where
  toFun := g ∘ f
  map_one_to_zero := by dsimp; rw [map_one, map_one_to_zero]

def OneZeroHom.comp_zero [FunLike F β γ] [IsZeroHom F β γ] (g: F) (f: α →₁₀ β) : α →₁₀ γ where
  toFun := g ∘ f
  map_one_to_zero := by dsimp; rw [map_one_to_zero, map_zero]

def OneHom.of_log_exp (g: β →₀₁ γ) (f: α →₁₀ β) : OneHom α γ where
  toFun := g ∘ f
  map_one := by dsimp; rw [map_one_to_zero, map_zero_to_one]

def ZeroHom.of_exp_log (g: β →₁₀ γ) (f: α →₀₁ β) : ZeroHom α γ where
  toFun := g ∘ f
  map_zero := by dsimp; rw [map_zero_to_one, map_one_to_zero]

def AddMulHom.add_comp [FunLike F α β] [IsAddHom F α β] (g: β →ₙₐ* γ) (f: F) : α →ₙₐ* γ where
  toFun := g ∘ f
  map_add_to_mul {a b} := by dsimp; rw [map_add, map_add_to_mul]

def AddMulHom.comp_mul [FunLike F β γ] [IsMulHom F β γ] (g: F) (f: α →ₙₐ* β) : α →ₙₐ* γ where
  toFun := g ∘ f
  map_add_to_mul {a b} := by dsimp; rw [map_add_to_mul, map_mul]

def MulAddHom.mul_comp [FunLike F α β] [IsMulHom F α β] (g: β →ₙₘ+ γ) (f: F) : α →ₙₘ+ γ where
  toFun := g ∘ f
  map_mul_to_add {a b} := by dsimp; rw [map_mul, map_mul_to_add]

def MulAddHom.comp_add [FunLike F β γ] [IsAddHom F β γ] (g: F) (f: α →ₙₘ+ β) : α →ₙₘ+ γ where
  toFun := g ∘ f
  map_mul_to_add {a b} := by dsimp; rw [map_mul_to_add, map_add]

def MulHom.of_log_exp (g: β →ₙₐ* γ) (f: α →ₙₘ+ β) : MulHom α γ where
  toFun := g ∘ f
  map_mul {a b} := by dsimp; rw [map_mul_to_add, map_add_to_mul]

def AddHom.of_exp_log (g: β →ₙₘ+ γ) (f: α →ₙₐ* β) : AddHom α γ where
  toFun := g ∘ f
  map_add {a b} := by dsimp; rw [map_add_to_mul, map_mul_to_add]

def ExpHom.add_comp [FunLike F α β] [IsZeroHom F α β] [IsAddHom F α β] (g: β →ₐ* γ) (f: F) : α →ₐ* γ := {
  AddMulHom.add_comp g.toAddMulHom f, ZeroOneHom.zero_comp g.toZeroOneHom f with
}

def ExpHom.comp_mul [FunLike F β γ] [IsOneHom F β γ] [IsMulHom F β γ] (g: F) (f: α →ₐ* β) : α →ₐ* γ := {
  AddMulHom.comp_mul g f.toAddMulHom, ZeroOneHom.comp_one g f.toZeroOneHom with
}

def LogHom.mul_comp [FunLike F α β] [IsOneHom F α β] [IsMulHom F α β] (g: β →ₘ+ γ) (f: F) : α →ₘ+ γ := {
  MulAddHom.mul_comp g.toMulAddHom f, OneZeroHom.one_comp g.toOneZeroHom f with
}

def LogHom.comp_add [FunLike F β γ] [IsZeroHom F β γ] [IsAddHom F β γ] (g: F) (f: α →ₘ+ β) : α →ₘ+ γ := {
  MulAddHom.comp_add g f.toMulAddHom, OneZeroHom.comp_zero g f.toOneZeroHom with
}

def GroupHom.of_log_exp (g: β →ₐ* γ) (f: α →ₘ+ β) : α →* γ := {
  MulHom.of_log_exp g.toAddMulHom f.toMulAddHom, OneHom.of_log_exp g.toZeroOneHom f.toOneZeroHom with
}

def AddGroupHom.of_exp_log (g: β →ₘ+ γ) (f: α →ₐ* β) : α →+ γ := {
  AddHom.of_exp_log g.toMulAddHom f.toAddMulHom, ZeroHom.of_exp_log g.toOneZeroHom f.toZeroOneHom with
}

@[simp] def AddGroupHom.apply_comp (a: β →+ γ) (b: α →+ β) : a.comp b x = a (b x) := rfl
@[simp] def AddGroupWithOneHom.apply_comp (a: β →+₁ γ) (b: α →+₁ β) : a.comp b x = a (b x) := rfl
@[simp] def GroupHom.apply_comp (a: β →* γ) (b: α →* β) : a.comp b x = a (b x) := rfl
@[simp] def GroupWithZeroHom.apply_comp (a: β →*₀ γ) (b: α →*₀ β) : a.comp b x = a (b x) := rfl
@[simp] def RngHom.apply_comp (a: β →+*₀ γ) (b: α →+*₀ β) : a.comp b x = a (b x) := rfl
@[simp] def RingHom.apply_comp (a: β →+* γ) (b: α →+* β) : a.comp b x = a (b x) := rfl
@[simp] def LinearMap.apply_comp (a: β →ₗ[R] γ) (b: α →ₗ[R] β) : a.comp b x = a (b x) := rfl
@[simp] def AlgHom.apply_comp (a: β →ₐ[R] γ) (b: α →ₐ[R] β) : a.comp b x = a (b x) := rfl

@[simp] def ZeroOneHom.apply_zero_comp [FunLike F α β] [IsZeroHom F α β] (g: β →₀₁ γ) (f: F) : zero_comp g f x = g (f x) := rfl
@[simp] def ZeroOneHom.apply_comp_one [FunLike F β γ] [IsOneHom F β γ] (g: F) (f: α →₀₁ β) : comp_one g f x = g (f x) := rfl
@[simp] def OneZeroHom.apply_one_comp [FunLike F α β] [IsOneHom F α β] (g: β →₁₀ γ) (f: F) : one_comp g f x = g (f x) := rfl
@[simp] def OneZeroHom.apply_comp_zero [FunLike F β γ] [IsZeroHom F β γ] (g: F) (f: α →₁₀ β) : comp_zero g f x = g (f x) := rfl
@[simp] def OneHom.apply_of_log_exp (g: β →₀₁ γ) (f: α →₁₀ β) : of_log_exp g f x = g (f x) := rfl
@[simp] def ZeroHom.apply_of_exp_log (g: β →₁₀ γ) (f: α →₀₁ β) : of_exp_log g f x = g (f x) := rfl

@[simp] def AddMulHom.apply_add_comp [FunLike F α β] [IsAddHom F α β] (g: β →ₙₐ* γ) (f: F) : add_comp g f x = g (f x) := rfl
@[simp] def AddMulHom.apply_comp_mul [FunLike F β γ] [IsMulHom F β γ] (g: F) (f: α →ₙₐ* β) : comp_mul g f x = g (f x) := rfl
@[simp] def MulAddHom.apply_mul_comp [FunLike F α β] [IsMulHom F α β] (g: β →ₙₘ+ γ) (f: F) : mul_comp g f x = g (f x) := rfl
@[simp] def MulAddHom.apply_comp_add [FunLike F β γ] [IsAddHom F β γ] (g: F) (f: α →ₙₘ+ β) : comp_add g f x = g (f x) := rfl
@[simp] def MulHom.apply_of_log_exp (g: β →ₙₐ* γ) (f: α →ₙₘ+ β) : of_log_exp g f x = g (f x) := rfl
@[simp] def AddHom.apply_of_exp_log (g: β →ₙₘ+ γ) (f: α →ₙₐ* β) : of_exp_log g f x = g (f x) := rfl

@[simp] def ExpHom.apply_add_comp [FunLike F α β] [IsZeroHom F α β] [IsAddHom F α β] (g: β →ₐ* γ) (f: F) : add_comp g f x = g (f x) := rfl
@[simp] def ExpHom.apply_comp_mul [FunLike F β γ] [IsOneHom F β γ] [IsMulHom F β γ] (g: F) (f: α →ₐ* β) : comp_mul g f x = g (f x) := rfl
@[simp] def LogHom.apply_mul_comp [FunLike F α β] [IsOneHom F α β] [IsMulHom F α β] (g: β →ₘ+ γ) (f: F) : mul_comp g f x = g (f x) := rfl
@[simp] def LogHom.apply_comp_add [FunLike F β γ] [IsZeroHom F β γ] [IsAddHom F β γ] (g: F) (f: α →ₘ+ β) : comp_add g f x = g (f x) := rfl
@[simp] def GroupHom.apply_of_log_exp (g: β →ₐ* γ) (f: α →ₘ+ β) : of_log_exp g f x = g (f x) := rfl
@[simp] def AddGroupHom.apply_of_exp_log (g: β →ₘ+ γ) (f: α →ₐ* β) : of_exp_log g f x = g (f x) := rfl

@[simp]
def mul_comp_comp_of_log_exp
  (g: α →* β) (h: γ →ₐ* δ) (f: β →ₘ+ γ) :
  GroupHom.of_log_exp h (LogHom.mul_comp f g) =
  (GroupHom.of_log_exp h f).comp g := rfl

@[simp]
def add_comp_comp_of_exp_log
  (g: α →+ β) (h: γ →ₘ+ δ) (f: β →ₐ* γ) :
  AddGroupHom.of_exp_log h (ExpHom.add_comp f g) =
  (AddGroupHom.of_exp_log h f).comp g := rfl

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

def LinearEmbedding.refl : α ↪ₗ[R] α := {
  Embedding.rfl, LinearMap.id _ with
}

def AlgEmbedding.refl : α ↪ₐ[R] α := {
  Embedding.rfl, AlgHom.id _ with
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

def LinearEquiv.refl : α ≃ₗ[R] α := {
  Equiv.rfl, LinearMap.id _ with
}

def AlgEquiv.refl : α ≃ₐ[R] α := {
  Equiv.rfl, AlgHom.id _ with
}

@[simp] def AddGroupEmbedding.apply_refl (x: α): AddGroupEmbedding.refl x = x := rfl
@[simp] def AddGroupWithOneEmbedding.apply_refl (x: α): AddGroupWithOneEmbedding.refl x = x := rfl
@[simp] def GroupEmbedding.apply_refl (x: α): GroupEmbedding.refl x = x := rfl
@[simp] def GroupWithZeroEmbedding.apply_refl (x: α): GroupWithZeroEmbedding.refl x = x := rfl
@[simp] def RngEmbedding.apply_refl (x: α): RngEmbedding.refl x = x := rfl
@[simp] def RingEmbedding.apply_refl (x: α): RingEmbedding.refl x = x := rfl
@[simp] def LinearEmbedding.apply_refl (x: α): LinearEmbedding.refl (R := R) x = x := rfl
@[simp] def AlgEmbedding.apply_refl (x: α): AlgEmbedding.refl (R := R) x = x := rfl

@[simp] def AddGroupEquiv.apply_refl (x: α): AddGroupEquiv.refl x = x := rfl
@[simp] def AddGroupWithOneEquiv.apply_refl (x: α): AddGroupWithOneEquiv.refl x = x := rfl
@[simp] def GroupEquiv.apply_refl (x: α): GroupEquiv.refl x = x := rfl
@[simp] def GroupWithZeroEquiv.apply_refl (x: α): GroupWithZeroEquiv.refl x = x := rfl
@[simp] def RngEquiv.apply_refl (x: α): RngEquiv.refl x = x := rfl
@[simp] def RingEquiv.apply_refl (x: α): RingEquiv.refl x = x := rfl
@[simp] def LinearEquiv.apply_refl (x: α): LinearEquiv.refl (R := R) x = x := rfl
@[simp] def AlgEquiv.apply_refl (x: α): AlgEquiv.refl (R := R) x = x := rfl

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

def LinearEmbedding.trans (h: α ↪ₗ[R] β) (g: β ↪ₗ[R] γ) : α ↪ₗ[R] γ := {
  h.toEmbedding.trans g.toEmbedding, g.toLinearMap.comp h.toLinearMap with
}

def AlgEmbedding.trans (h: α ↪ₐ[R] β) (g: β ↪ₐ[R] γ) : α ↪ₐ[R] γ := {
  h.toEmbedding.trans g.toEmbedding, g.toAlgHom.comp h.toAlgHom with
}

def ExpEmbedding.add_trans [EmbeddingLike F α β] [IsZeroHom F α β] [IsAddHom F α β] (f: F) (g: β ↪ₐ* γ) : α ↪ₐ* γ := {
  Embedding.trans (f: α ↪ β) g.toEmbedding, ExpHom.add_comp g.toExpHom f with
}

def ExpEmbedding.trans_mul [EmbeddingLike F β γ] [IsOneHom F β γ] [IsMulHom F β γ] (f: α ↪ₐ* β) (g: F) : α ↪ₐ* γ := {
  Embedding.trans f.toEmbedding (g: β ↪ γ), ExpHom.comp_mul g f.toExpHom with
}

def LogEmbedding.mul_trans [EmbeddingLike F α β] [IsOneHom F α β] [IsMulHom F α β] (f: F) (g: β ↪ₘ+ γ) : α ↪ₘ+ γ := {
  Embedding.trans (f: α ↪ β) g.toEmbedding, LogHom.mul_comp g.toLogHom f with
}

def LogEmbedding.trans_add [EmbeddingLike F β γ] [IsZeroHom F β γ] [IsAddHom F β γ] (f: α ↪ₘ+ β) (g: F) : α ↪ₘ+ γ := {
  Embedding.trans f.toEmbedding (g: β ↪ γ), LogHom.comp_add g f.toLogHom with
}

def GroupEmbedding.of_log_exp (f: α ↪ₘ+ β) (g: β ↪ₐ* γ) : α ↪* γ := {
  Embedding.trans f.toEmbedding (g: β ↪ γ), GroupHom.of_log_exp g.toExpHom f.toLogHom with
}

def AddGroupEmbedding.of_exp_log (f: α ↪ₐ* β) (g: β ↪ₘ+ γ) : α ↪+ γ := {
  Embedding.trans f.toEmbedding (g: β ↪ γ), AddGroupHom.of_exp_log g.toLogHom f.toExpHom with
}

@[simp] def AddGroupEmbedding.apply_trans (a: β ↪+ γ) (b: α ↪+ β) : b.trans a x = a (b x) := rfl
@[simp] def AddGroupWithOneEmbedding.apply_trans (a: β ↪+₁ γ) (b: α ↪+₁ β) : b.trans a x = a (b x) := rfl
@[simp] def GroupEmbedding.apply_trans (a: β ↪* γ) (b: α ↪* β) : b.trans a x = a (b x) := rfl
@[simp] def GroupWithZeroEmbedding.apply_trans (a: β ↪*₀ γ) (b: α ↪*₀ β) : b.trans a x = a (b x) := rfl
@[simp] def RngEmbedding.apply_trans (a: β ↪+*₀ γ) (b: α ↪+*₀ β) : b.trans a x = a (b x) := rfl
@[simp] def RingEmbedding.apply_trans (a: β ↪+* γ) (b: α ↪+* β) : b.trans a x = a (b x) := rfl
@[simp] def LinearEmbedding.apply_trans (a: β ↪ₗ[R] γ) (b: α ↪ₗ[R] β) : b.trans a x = a (b x) := rfl
@[simp] def AlgEmbedding.apply_trans (a: β ↪ₐ[R] γ) (b: α ↪ₐ[R] β) : b.trans a x = a (b x) := rfl
@[simp] def ExpEmbedding.apply_add_trans [EmbeddingLike F α β] [IsZeroHom F α β] [IsAddHom F α β] (g: β ↪ₐ* γ) (f: F) : add_trans f g x = g (f x) := rfl
@[simp] def ExpEmbedding.apply_trans_mul [EmbeddingLike F β γ] [IsOneHom F β γ] [IsMulHom F β γ] (g: F) (f: α ↪ₐ* β) : trans_mul f g x = g (f x) := rfl
@[simp] def LogEmbedding.apply_mul_trans [EmbeddingLike F α β] [IsOneHom F α β] [IsMulHom F α β] (g: β ↪ₘ+ γ) (f: F) : mul_trans f g x = g (f x) := rfl
@[simp] def LogEmbedding.apply_trans_add [EmbeddingLike F β γ] [IsZeroHom F β γ] [IsAddHom F β γ] (g: F) (f: α ↪ₘ+ β) : trans_add f g x = g (f x) := rfl
@[simp] def GroupEmbedding.apply_of_log_exp (f: α ↪ₘ+ β) (g: β ↪ₐ* γ) : of_log_exp f g x = g (f x) := rfl
@[simp] def AddGroupEmbedding.apply_of_exp_log (f: α ↪ₐ* β) (g: β ↪ₘ+ γ) : of_exp_log f g x = g (f x) := rfl

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

def LinearEquiv.trans (h: α ≃ₗ[R] β) (g: β ≃ₗ[R] γ) : α ≃ₗ[R] γ := {
  h.toEquiv.trans g.toEquiv, g.toLinearMap.comp h.toLinearMap with
}

def AlgEquiv.trans (h: α ≃ₐ[R] β) (g: β ≃ₐ[R] γ) : α ≃ₐ[R] γ := {
  h.toEquiv.trans g.toEquiv, g.toAlgHom.comp h.toAlgHom with
}

def ExpEquiv.add_trans [EquivLike F α β] [IsZeroHom F α β] [IsAddHom F α β] (f: F) (g: β ≃ₐ* γ) : α ≃ₐ* γ := {
  Equiv.trans (f: α ≃ β) g.toEquiv, ExpHom.add_comp g.toExpHom f with
}

def ExpEquiv.trans_mul [EquivLike F β γ] [IsOneHom F β γ] [IsMulHom F β γ] (f: α ≃ₐ* β) (g: F) : α ≃ₐ* γ := {
  Equiv.trans f.toEquiv (g: β ≃ γ), ExpHom.comp_mul g f.toExpHom with
}

def LogEquiv.mul_trans [EquivLike F α β] [IsOneHom F α β] [IsMulHom F α β] (f: F) (g: β ≃ₘ+ γ) : α ≃ₘ+ γ := {
  Equiv.trans (f: α ≃ β) g.toEquiv, LogHom.mul_comp g.toLogHom f with
}

def LogEquiv.trans_add [EquivLike F β γ] [IsZeroHom F β γ] [IsAddHom F β γ] (f: α ≃ₘ+ β) (g: F) : α ≃ₘ+ γ := {
  Equiv.trans f.toEquiv (g: β ≃ γ), LogHom.comp_add g f.toLogHom with
}

def GroupEquiv.of_log_exp (f: α ≃ₘ+ β) (g: β ≃ₐ* γ) : α ≃* γ := {
  Equiv.trans f.toEquiv (g: β ≃ γ), GroupHom.of_log_exp g.toExpHom f.toLogHom with
}

def AddGroupEquiv.of_exp_log (f: α ≃ₐ* β) (g: β ≃ₘ+ γ) : α ≃+ γ := {
  Equiv.trans f.toEquiv (g: β ≃ γ), AddGroupHom.of_exp_log g.toLogHom f.toExpHom with
}

@[simp] def AddGroupEquiv.apply_trans (a: β ≃+ γ) (b: α ≃+ β) : b.trans a x = a (b x) := rfl
@[simp] def AddGroupWithOneEquiv.apply_trans (a: β ≃+₁ γ) (b: α ≃+₁ β) : b.trans a x = a (b x) := rfl
@[simp] def GroupEquiv.apply_trans (a: β ≃* γ) (b: α ≃* β) : b.trans a x = a (b x) := rfl
@[simp] def GroupWithZeroEquiv.apply_trans (a: β ≃*₀ γ) (b: α ≃*₀ β) : b.trans a x = a (b x) := rfl
@[simp] def RngEquiv.apply_trans (a: β ≃+*₀ γ) (b: α ≃+*₀ β) : b.trans a x = a (b x) := rfl
@[simp] def RingEquiv.apply_trans (a: β ≃+* γ) (b: α ≃+* β) : b.trans a x = a (b x) := rfl
@[simp] def LinearEquiv.apply_trans (a: β ≃ₗ[R] γ) (b: α ≃ₗ[R] β) : b.trans a x = a (b x) := rfl
@[simp] def AlgEquiv.apply_trans (a: β ≃ₐ[R] γ) (b: α ≃ₐ[R] β) : b.trans a x = a (b x) := rfl
@[simp] def ExpEquiv.apply_add_trans [EquivLike F α β] [IsZeroHom F α β] [IsAddHom F α β] (g: β ≃ₐ* γ) (f: F) : add_trans f g x = g (f x) := rfl
@[simp] def ExpEquiv.apply_trans_mul [EquivLike F β γ] [IsOneHom F β γ] [IsMulHom F β γ] (g: F) (f: α ≃ₐ* β) : trans_mul f g x = g (f x) := rfl
@[simp] def LogEquiv.apply_mul_trans [EquivLike F α β] [IsOneHom F α β] [IsMulHom F α β] (g: β ≃ₘ+ γ) (f: F) : mul_trans f g x = g (f x) := rfl
@[simp] def LogEquiv.apply_trans_add [EquivLike F β γ] [IsZeroHom F β γ] [IsAddHom F β γ] (g: F) (f: α ≃ₘ+ β) : trans_add f g x = g (f x) := rfl
@[simp] def GroupEquiv.apply_of_log_exp (f: α ≃ₘ+ β) (g: β ≃ₐ* γ) : of_log_exp f g x = g (f x) := rfl
@[simp] def AddGroupEquiv.apply_of_exp_log (f: α ≃ₐ* β) (g: β ≃ₘ+ γ) : of_exp_log f g x = g (f x) := rfl

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

def SMulEquiv.symm (h: SMulEquiv R α β) : SMulEquiv R β α where
  toEquiv := h.toEquiv.symm
  map_smul {a b} := by
    rw [←h.coe_symm (_ • _)]
    show h.toEquiv.symm _ = h.toEquiv.symm (h.toFun _)
    erw [h.map_smul, h.rightInv]

def AlgebraMapEquiv.symm (h: AlgebraMapEquiv R α β) : AlgebraMapEquiv R β α where
  toEquiv := h.toEquiv.symm
  map_algebraMap {r} := by
    rw [←h.coe_symm (algebraMap _)]
    show h.toEquiv.symm _ = h.toEquiv.symm (h.toFun _)
    erw [h.map_algebraMap]

def ZeroOneEquiv.symm (h: α ≃₀₁ β) : β ≃₁₀ α where
  toEquiv := h.toEquiv.symm
  map_one_to_zero := by
    rw [←h.coe_symm 0]
    show h.toEquiv.symm _ = h.toEquiv.symm (h.toFun _)
    erw [h.map_zero_to_one]

def OneZeroEquiv.symm (h: α ≃₁₀ β) : β ≃₀₁ α where
  toEquiv := h.toEquiv.symm
  map_zero_to_one := by
    rw [←h.coe_symm 1]
    show h.toEquiv.symm _ = h.toEquiv.symm (h.toFun _)
    erw [h.map_one_to_zero]

def AddMulEquiv.symm (h: α ≃ₙₐ* β) : β ≃ₙₘ+ α where
  toEquiv := h.toEquiv.symm
  map_mul_to_add {a b} := by
    rw [←h.coe_symm (_ + _)]
    show h.toEquiv.symm _ = h.toEquiv.symm (h.toFun _)
    erw [h.map_add_to_mul, h.rightInv, h.rightInv]

def MulAddEquiv.symm (h: α ≃ₙₘ+ β) : β ≃ₙₐ* α where
  toEquiv := h.toEquiv.symm
  map_add_to_mul {a b} := by
    rw [←h.coe_symm (_ * _)]
    show h.toEquiv.symm _ = h.toEquiv.symm (h.toFun _)
    erw [h.map_mul_to_add, h.rightInv, h.rightInv]

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

def LinearEquiv.symm (h: α ≃ₗ[R] β) : β ≃ₗ[R] α := {
  h.toAddEquiv.symm,  h.toSMulEquiv.symm with
}

def AlgEquiv.symm (h: α ≃ₐ[R] β) : β ≃ₐ[R] α := {
  h.toAddEquiv.symm, h.toMulEquiv.symm, h.toAlgebraMapEquiv.symm with
}

def ExpEquiv.symm (h: α ≃ₐ* β) : β ≃ₘ+ α := {
  h.toAddMulEquiv.symm, h.toZeroOneEquiv.symm with
}

def LogEquiv.symm (h: α ≃ₘ+ β) : β ≃ₐ* α := {
  h.toMulAddEquiv.symm, h.toOneZeroEquiv.symm with
}

@[simp] def AddGroupEquiv.symm_symm (a: α ≃+ β) : a.symm.symm = a := rfl
@[simp] def AddGroupWithOneEquiv.symm_symm (a: α ≃+₁ β) : a.symm.symm = a := rfl
@[simp] def GroupEquiv.symm_symm (a: α ≃* β) : a.symm.symm = a := rfl
@[simp] def GroupWithZeroEquiv.symm_symm (a: α ≃*₀ β) : a.symm.symm = a := rfl
@[simp] def RngEquiv.symm_symm (a: α ≃+*₀ β) : a.symm.symm = a := rfl
@[simp] def RingEquiv.symm_symm (a: α ≃+* β) : a.symm.symm = a := rfl
@[simp] def LinearEquiv.symm_symm (a: α ≃ₗ[R] β) : a.symm.symm = a := rfl
@[simp] def AlgEquiv.symm_symm (a: α ≃ₐ[R] β) : a.symm.symm = a := rfl
@[simp] def ExpEquiv.symm_symm (a: α ≃ₐ* β) : a.symm.symm = a := rfl
@[simp] def LogEquiv.symm_symm (a: α ≃ₘ+ β) : a.symm.symm = a := rfl

def AddGroupEmbedding.toHom (h: α ↪+ β) : α →+ β := h
def AddGroupWithOneEmbedding.toHom (h: α ↪+₁ β) : α →+₁ β := h
def GroupEmbedding.toHom (h: α ↪* β) : α →* β := h
def GroupWithZeroEmbedding.toHom (h: α ↪*₀ β) : α →*₀ β := h
def RingEmbedding.toHom (h: α ↪+* β) : α →+* β := h
def RngEmbedding.toHom (h: α ↪+*₀ β) : α →+*₀ β := h
def LinearEmbedding.toHom (h: α ↪ₗ[R] β) : α →ₗ[R] β := h
def AlgEmbedding.toHom (h: α ↪ₐ[R] β) : α →ₐ[R] β := h
def ExpEmbedding.toHom (h: α ↪ₐ* β) : α →ₐ* β := h
def LogEmbedding.toHom (h: α ↪ₘ+ β) : α →ₘ+ β := h

def AddGroupEquiv.toEmbedding (h: α ≃+ β) : α ↪+ β := h
def AddGroupWithOneEquiv.toEmbedding (h: α ≃+₁ β) : α ↪+₁ β := h
def GroupEquiv.toEmbedding (h: α ≃* β) : α ↪* β := h
def GroupWithZeroEquiv.toEmbedding (h: α ≃*₀ β) : α ↪*₀ β := h
def RingEquiv.toEmbedding (h: α ≃+* β) : α ↪+* β := h
def RngEquiv.toEmbedding (h: α ≃+*₀ β) : α ↪+*₀ β := h
def LinearEquiv.toEmbedding (h: α ≃ₗ[R] β) : α ↪ₗ[R] β := h
def AlgEquiv.toEmbedding (h: α ≃ₐ[R] β) : α ↪ₐ[R] β := h
def ExpEquiv.toEmbedding (h: α ≃ₐ* β) : α ↪ₐ* β := h
def LogEquiv.toEmbedding (h: α ≃ₘ+ β) : α ↪ₘ+ β := h

def AddGroupEquiv.toHom (h: α ≃+ β) : α →+ β := h
def AddGroupWithOneEquiv.toHom (h: α ≃+₁ β) : α →+₁ β := h
def GroupEquiv.toHom (h: α ≃* β) : α →* β := h
def GroupWithZeroEquiv.toHom (h: α ≃*₀ β) : α →*₀ β := h
def RingEquiv.toHom (h: α ≃+* β) : α →+* β := h
def RngEquiv.toHom (h: α ≃+*₀ β) : α →+*₀ β := h
def LinearEquiv.toHom (h: α ≃ₗ[R] β) : α →ₗ[R] β := h
def AlgEquiv.toHom (h: α ≃ₐ[R] β) : α →ₐ[R] β := h
def ExpEquiv.toHom (h: α ≃ₐ* β) : α →ₐ* β := h
def LogEquiv.toHom (h: α ≃ₘ+ β) : α →ₘ+ β := h

@[simp] def AddGroupEquiv.coe_symm (h: α ≃+ β) (x: α) : h.symm (h x) = x := Equiv.coe_symm _ _
@[simp] def AddGroupEquiv.symm_coe (h: α ≃+ β) (x: β) : h (h.symm x) = x := Equiv.symm_coe _ _
@[simp] def AddGroupWithOneEquiv.coe_symm (h: α ≃+₁ β) (x: α) : h.symm (h x) = x := Equiv.coe_symm _ _
@[simp] def AddGroupWithOneEquiv.symm_coe (h: α ≃+₁ β) (x: β) : h (h.symm x) = x := Equiv.symm_coe _ _
@[simp] def GroupEquiv.coe_symm (h: α ≃* β) (x: α) : h.symm (h x) = x := Equiv.coe_symm _ _
@[simp] def GroupEquiv.symm_coe (h: α ≃* β) (x: β) : h (h.symm x) = x := Equiv.symm_coe _ _
@[simp] def GroupWithZeroEquiv.coe_symm (h: α ≃*₀ β) (x: α) : h.symm (h x) = x := Equiv.coe_symm _ _
@[simp] def GroupWithZeroEquiv.symm_coe (h: α ≃*₀ β) (x: β) : h (h.symm x) = x := Equiv.symm_coe _ _
@[simp] def RingEquiv.coe_symm (h: α ≃+* β) (x: α) : h.symm (h x) = x := Equiv.coe_symm _ _
@[simp] def RingEquiv.symm_coe (h: α ≃+* β) (x: β) : h (h.symm x) = x := Equiv.symm_coe _ _
@[simp] def RngEquiv.coe_symm (h: α ≃+*₀ β) (x: α) : h.symm (h x) = x := Equiv.coe_symm _ _
@[simp] def RngEquiv.symm_coe (h: α ≃+*₀ β) (x: β) : h (h.symm x) = x := Equiv.symm_coe _ _
@[simp] def LinearEquiv.coe_symm (h: α ≃ₗ[R] β) (x: α) : h.symm (h x) = x := Equiv.coe_symm _ _
@[simp] def LinearEquiv.symm_coe (h: α ≃ₗ[R] β) (x: β) : h (h.symm x) = x := Equiv.symm_coe _ _
@[simp] def AlgEquiv.coe_symm (h: α ≃ₐ[R] β) (x: α) : h.symm (h x) = x := Equiv.coe_symm _ _
@[simp] def AlgEquiv.symm_coe (h: α ≃ₐ[R] β) (x: β) : h (h.symm x) = x := Equiv.symm_coe _ _
@[simp] def AddMulEquiv.coe_symm (h: α ≃ₐ* β) (x: α) : h.symm (h x) = x := Equiv.coe_symm _ _
@[simp] def AddMulEquiv.symm_coe (h: α ≃ₐ* β) (x: β) : h (h.symm x) = x := Equiv.symm_coe _ _
@[simp] def MulAddEquiv.coe_symm (h: α ≃ₘ+ β) (x: α) : h.symm (h x) = x := Equiv.coe_symm _ _
@[simp] def MulAddEquiv.symm_coe (h: α ≃ₘ+ β) (x: β) : h (h.symm x) = x := Equiv.symm_coe _ _

@[simp] def AddGroupEquiv.trans_symm (h: α ≃+ β) : h.trans h.symm = .refl := by hom_equiv_trans_symm_impl h
@[simp] def AddGroupEquiv.symm_trans (h: α ≃+ β) : h.symm.trans h = .refl := by hom_equiv_trans_symm_impl h
@[simp] def AddGroupWithOneEquiv.trans_symm (h: α ≃+₁ β) : h.trans h.symm = .refl := by hom_equiv_trans_symm_impl h
@[simp] def AddGroupWithOneEquiv.symm_trans (h: α ≃+₁ β) : h.symm.trans h = .refl := by hom_equiv_trans_symm_impl h
@[simp] def GroupEquiv.trans_symm (h: α ≃* β) : h.trans h.symm = .refl := by hom_equiv_trans_symm_impl h
@[simp] def GroupEquiv.symm_trans (h: α ≃* β) : h.symm.trans h = .refl := by hom_equiv_trans_symm_impl h
@[simp] def GroupWithZeroEquiv.trans_symm (h: α ≃*₀ β) : h.trans h.symm = .refl := by hom_equiv_trans_symm_impl h
@[simp] def GroupWithZeroEquiv.symm_trans (h: α ≃*₀ β) : h.symm.trans h = .refl := by hom_equiv_trans_symm_impl h
@[simp] def RingEquiv.trans_symm (h: α ≃+* β) : h.trans h.symm = .refl := by hom_equiv_trans_symm_impl h
@[simp] def RingEquiv.symm_trans (h: α ≃+* β) : h.symm.trans h = .refl := by hom_equiv_trans_symm_impl h
@[simp] def RngEquiv.trans_symm (h: α ≃+*₀ β) : h.trans h.symm = .refl := by hom_equiv_trans_symm_impl h
@[simp] def RngEquiv.symm_trans (h: α ≃+*₀ β) : h.symm.trans h = .refl := by hom_equiv_trans_symm_impl h
@[simp] def LinearEquiv.trans_symm (h: α ≃ₗ[R] β) : h.trans h.symm = .refl := by hom_equiv_trans_symm_impl h
@[simp] def LinearEquiv.symm_trans (h: α ≃ₗ[R] β) : h.symm.trans h = .refl := by hom_equiv_trans_symm_impl h
@[simp] def AlgEquiv.trans_symm (h: α ≃ₐ[R] β) : h.trans h.symm = .refl := by hom_equiv_trans_symm_impl h
@[simp] def AlgEquiv.symm_trans (h: α ≃ₐ[R] β) : h.symm.trans h = .refl := by hom_equiv_trans_symm_impl h
@[simp] def ExpEquiv.trans_symm (h: α ≃ₐ* β) : AddGroupEquiv.of_exp_log h h.symm = .refl := by hom_equiv_trans_symm_impl h
@[simp] def ExpEquiv.symm_trans (h: α ≃ₐ* β) : GroupEquiv.of_log_exp h.symm h = .refl := by hom_equiv_trans_symm_impl h
@[simp] def LogEquiv.trans_symm (h: α ≃ₘ+ β) : GroupEquiv.of_log_exp h h.symm = .refl := by hom_equiv_trans_symm_impl h
@[simp] def LogEquiv.symm_trans (h: α ≃ₘ+ β) : AddGroupEquiv.of_exp_log h.symm h = .refl := by hom_equiv_trans_symm_impl h

protected def ExpEquiv.MulOfAdd (α: Type*) [Zero α] [Add α] : α ≃ₐ* MulOfAdd α where
  toFun := MulOfAdd.mk
  invFun := MulOfAdd.get
  leftInv _ := rfl
  rightInv _ := rfl
  map_add_to_mul := rfl
  map_zero_to_one := rfl

protected def LogEquiv.AddOfMul (α: Type*) [One α] [Mul α] : α ≃ₘ+ AddOfMul α where
  toFun := AddOfMul.mk
  invFun := AddOfMul.get
  leftInv _ := rfl
  rightInv _ := rfl
  map_mul_to_add := rfl
  map_one_to_zero := rfl

protected def ExpEquiv.AddOfMul (α: Type*) [One α] [Mul α] : AddOfMul α ≃ₐ* α :=
  (LogEquiv.AddOfMul α).symm

protected def LogEquiv.MulOfAdd (α: Type*) [Zero α] [Add α] : MulOfAdd α ≃ₘ+ α :=
  (ExpEquiv.MulOfAdd α).symm

protected def ExpHom.toMulOfAdd (α: Type*) [Zero α] [Add α] : α →ₐ* MulOfAdd α :=
  (ExpEquiv.MulOfAdd α).toHom

protected def LogHom.toAddOfMul (α: Type*) [One α] [Mul α] : α →ₘ+ AddOfMul α :=
  (LogEquiv.AddOfMul α).toHom

protected def ExpHom.ofAddOfMul (α: Type*) [One α] [Mul α] : AddOfMul α →ₐ* α :=
  (ExpEquiv.AddOfMul α).toHom

protected def LogHom.ofMulOfAdd (α: Type*) [Zero α] [Add α] : MulOfAdd α →ₘ+ α :=
  (LogEquiv.MulOfAdd α).toHom

@[simp] def ExpEquiv.apply_MulOfAdd : ExpEquiv.MulOfAdd α x = MulOfAdd.mk x := rfl
@[simp] def ExpEquiv.apply_AddOfMul : ExpEquiv.AddOfMul α x = AddOfMul.get x := rfl
@[simp] def LogEquiv.apply_MulOfAdd : LogEquiv.AddOfMul α x = AddOfMul.mk x := rfl
@[simp] def LogEquiv.apply_AddOfMul : LogEquiv.MulOfAdd α x = MulOfAdd.get x := rfl

@[simp] def ExpEquiv.symm_MulOfAdd : (ExpEquiv.MulOfAdd α).symm = (LogEquiv.MulOfAdd α) := rfl
@[simp] def ExpEquiv.symm_AddOfMul : (ExpEquiv.AddOfMul α).symm = (LogEquiv.AddOfMul α) := rfl
@[simp] def LogEquiv.symm_MulOfAdd : (LogEquiv.AddOfMul α).symm = (ExpEquiv.AddOfMul α) := rfl
@[simp] def LogEquiv.symm_AddOfMul : (LogEquiv.MulOfAdd α).symm = (ExpEquiv.MulOfAdd α) := rfl

@[simp] def ExpHom.apply_toMulOfAdd : ExpHom.toMulOfAdd α x = MulOfAdd.mk x := rfl
@[simp] def ExpHom.apply_ofAddOfMul : ExpHom.ofAddOfMul α x = AddOfMul.get x := rfl
@[simp] def LogHom.apply_toMulOfAdd : LogHom.toAddOfMul α x = AddOfMul.mk x := rfl
@[simp] def LogHom.apply_ofAddOfMul : LogHom.ofMulOfAdd α x = MulOfAdd.get x := rfl

def AddHom.toAddOpp (f: AddHom α β) (f_img_comm: ∀a b, f a + f b = f b + f a) : AddHom αᵃᵒᵖ β where
  toFun x := f x.get
  map_add {x y} := by
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
def LinearEmbedding.inj (h: α ↪ₗ[R] β) : Function.Injective h := Embedding.inj h.toEmbedding
def AlgEmbedding.inj (h: α ↪ₐ[R] β) : Function.Injective h := Embedding.inj h.toEmbedding
def ExpEmbedding.inj (h: α ↪ₐ* β) : Function.Injective h := Embedding.inj h.toEmbedding
def LogEmbedding.inj (h: α ↪ₘ+ β) : Function.Injective h := Embedding.inj h.toEmbedding

def AddGroupEquiv.inj (h: α ≃+ β) : Function.Injective h := Equiv.inj h.toEquiv
def AddGroupWithOneEquiv.inj (h: α ≃+₁ β) : Function.Injective h := Equiv.inj h.toEquiv
def GroupEquiv.inj (h: α ≃* β) : Function.Injective h := Equiv.inj h.toEquiv
def GroupWithZeroEquiv.inj (h: α ≃*₀ β) : Function.Injective h := Equiv.inj h.toEquiv
def RingEquiv.inj (h: α ≃+* β) : Function.Injective h := Equiv.inj h.toEquiv
def RngEquiv.inj (h: α ≃+*₀ β) : Function.Injective h := Equiv.inj h.toEquiv
def LinearEquiv.inj (h: α ≃ₗ[R] β) : Function.Injective h := Equiv.inj h.toEquiv
def AlgEquiv.inj (h: α ≃ₐ[R] β) : Function.Injective h := Equiv.inj h.toEquiv
def ExpEquiv.inj (h: α ≃ₐ* β) : Function.Injective h := Equiv.inj h.toEquiv
def LogEquiv.inj (h: α ≃ₘ+ β) : Function.Injective h := Equiv.inj h.toEquiv

@[ext] def AddGroupHom.ext (f g: α →+ β) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _
@[ext] def AddGroupWithOneHom.ext (f g: α →+₁ β) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _
@[ext] def GroupHom.ext (f g: α →* β) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _
@[ext] def GroupWithZeroHom.ext (f g: α →*₀ β) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _
@[ext] def RingHom.ext (f g: α →+* β) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _
@[ext] def LinearMap.ext (f g: α →ₗ[R] β) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _
@[ext] def AlgMap.ext (f g: α →ₐ[R] β) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _
@[ext] def ExpHom.ext (f g: α →ₐ* β) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _
@[ext] def LogHom.ext (f g: α →ₘ+ β) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _

@[ext] def AddGroupEmbedding.ext (f g: α ↪+ β) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _
@[ext] def AddGroupWithOneEmbedding.ext (f g: α ↪+₁ β) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _
@[ext] def GroupEmbedding.ext (f g: α ↪* β) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _
@[ext] def GroupWithZeroEmbedding.ext (f g: α ↪*₀ β) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _
@[ext] def RingEmbedding.ext (f g: α ↪+* β) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _
@[ext] def LinearEmbedding.ext (f g: α ↪ₗ[R] β) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _
@[ext] def AlgEmbedding.ext (f g: α ↪ₐ[R] β) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _
@[ext] def ExpEmbedding.ext (f g: α ↪ₐ* β) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _
@[ext] def LogEmbedding.ext (f g: α ↪ₘ+ β) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _

@[ext] def AddGroupEquiv.ext (f g: α ≃+ β) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _
@[ext] def AddGroupWithOneEquiv.ext (f g: α ≃+₁ β) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _
@[ext] def GroupEquiv.ext (f g: α ≃* β) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _
@[ext] def GroupWithZeroEquiv.ext (f g: α ≃*₀ β) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _
@[ext] def RingEquiv.ext (f g: α ≃+* β) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _
@[ext] def LinearEquiv.ext (f g: α ≃ₗ[R] β) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _
@[ext] def AlgEquiv.ext (f g: α ≃ₐ[R] β) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _
@[ext] def ExpEquiv.ext (f g: α ≃ₐ* β) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _
@[ext] def LogEquiv.ext (f g: α ≃ₘ+ β) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _

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

@[simp] def ZeroHom.toFun_eq_coe (f: ZeroHom α β) : f.toFun = f := rfl
@[simp] def OneHom.toFun_eq_coe (f: OneHom α β) : f.toFun = f := rfl
@[simp] def AddHom.toFun_eq_coe (f: AddHom α β) : f.toFun = f := rfl
@[simp] def MulHom.toFun_eq_coe (f: MulHom α β) : f.toFun = f := rfl
@[simp] def SMulHom.toFun_eq_coe (f: SMulHom R α β) : f.toFun = f := rfl

@[simp] def AddGroupHom.toFun_eq_coe (f: α →+ β) : f.toFun = f := rfl
@[simp] def GroupHom.toFun_eq_coe (f: α →* β) : f.toFun = f := rfl
@[simp] def AddGroupWithZeroHom.toFun_eq_coe (f: α →+₁ β) : f.toFun = f := rfl
@[simp] def GroupWithOneHom.toFun_eq_coe (f: α →*₀ β) : f.toFun = f := rfl
@[simp] def ExpHom.toFun_eq_coe (f: α →ₐ* β) : f.toFun = f := rfl
@[simp] def LogHom.toFun_eq_coe (f: α →ₘ+ β) : f.toFun = f := rfl
@[simp] def LinearEquiv.toLinearMap_eq_coe (f: α ≃ₗ[R] β) : (f.toLinearMap: α -> β) = f := rfl

@[simp] def AddGroupHom.toZeroHom_eq_coe (f: α →+ β) : (f.toZeroHom: _ -> _) = f := rfl
@[simp] def GroupHom.toOneHom_eq_coe (f: α →* β) : (f.toOneHom: _ -> _) = f := rfl
@[simp] def AddGroupWithZeroHom.toZeroHom_eq_coe (f: α →+₁ β) : (f.toZeroHom: _ -> _) = f := rfl
@[simp] def GroupWithOneHom.toOneHom_eq_coe (f: α →*₀ β) : (f.toOneHom: _ -> _) = f := rfl

@[simp] def AlgHom.toAddHom_eq_coe (f: α →ₐ[R] β) : (f.toAddHom: α -> β) = f := rfl

@[simp] def ExpEquiv.toHom_eq_coe (f: α ≃ₐ* β) : (f.toHom: _ -> _) = f := rfl
@[simp] def LogEquiv.toHom_eq_coe (f: α ≃ₘ+ β) : (f.toHom: _ -> _) = f := rfl
@[simp] def GroupEquiv.toHom_eq_coe (f: α ≃* β) : (f.toHom: _ -> _) = f := rfl
@[simp] def AddGroupEquiv.toHom_eq_coe (f: α ≃+ β) : (f.toHom: _ -> _) = f := rfl
@[simp] def GroupEquiv.of_log_exp_hom (g: α ≃ₘ+ β) (f: β ≃ₐ* α) : GroupHom.of_log_exp f.toHom g.toHom = (GroupEquiv.of_log_exp g f).toHom := rfl
@[simp] def AddGroupEquiv.of_exp_log_hom (f: α ≃ₘ+ β) (g: β ≃ₐ* α) : AddGroupHom.of_exp_log f.toHom g.toHom = (AddGroupEquiv.of_exp_log g f).toHom := rfl

def LinearEquiv.MulOpp (α: Type*) [SMul R α] [Add α] : α ≃ₗ[R] αᵐᵒᵖ where
  toEquiv := Equiv.MulOpp
  map_add := rfl
  map_smul := rfl

@[simp] def LinearEquiv.apply_mul_opp : LinearEquiv.MulOpp (R := R) α = MulOpp.mk (α := α) := rfl
@[simp] def LinearEquiv.symm_apply_mul_opp : (LinearEquiv.MulOpp (R := R) α).symm = MulOpp.get (α := α) := rfl

namespace Equiv

def congrExpHomToGroupHom (g: α ≃ₐ* γ) (h: β ≃* δ) : (α →ₐ* β) ≃ (γ →* δ) where
  toFun f := GroupHom.of_log_exp (ExpHom.comp_mul h.toHom f) g.symm.toHom
  invFun f := ExpHom.comp_mul h.symm.toHom (ExpHom.comp_mul f g.toHom)
  leftInv _ := by ext; simp
  rightInv _ := by ext; simp

def congrLogHomToGroupHom (g: α ≃* γ) (h: β ≃ₐ* δ) : (α →ₘ+ β) ≃ (γ →* δ) where
  toFun f := GroupHom.comp (GroupHom.of_log_exp h.toHom f) g.symm.toHom
  invFun f := LogHom.mul_comp h.symm.toHom (GroupHom.comp f g.toHom)
  leftInv _ := by ext; simp
  rightInv _ := by ext; simp

def congrGroupHomToAddGroupHom (g: α ≃ₘ+ γ) (h: β ≃ₘ+ δ) : (α →* β) ≃ (γ →+ δ) where
  toFun f := AddGroupHom.of_exp_log h.toHom (ExpHom.comp_mul f g.symm.toHom)
  invFun f := GroupHom.of_log_exp h.symm.toHom (LogHom.comp_add f g.toHom)
  leftInv _ := by ext; simp
  rightInv _ := by ext; simp

def congrAddGroupHomToGroupHom (g: α ≃ₐ* γ) (h: β ≃ₐ* δ) : (α →+ β) ≃ (γ →* δ) :=
  (congrGroupHomToAddGroupHom g.symm h.symm).symm

def congrExpHomToAddGroupHom (g: α ≃+ γ) (h: β ≃ₘ+ δ) : (α →ₐ* β) ≃ (γ →+ δ) := by
  apply Equiv.trans _ (congrGroupHomToAddGroupHom (LogEquiv.MulOfAdd _) (LogEquiv.MulOfAdd _))
  apply congrExpHomToGroupHom
  apply ExpEquiv.add_trans g (ExpEquiv.MulOfAdd _)
  apply GroupEquiv.of_log_exp h (ExpEquiv.MulOfAdd _)

def congrLogHomToAddGroupHom (g: α ≃ₘ+ γ) (h: β ≃+ δ) : (α →ₘ+ β) ≃ (γ →+ δ) := by
  apply Equiv.trans _ (congrGroupHomToAddGroupHom (LogEquiv.MulOfAdd _) (LogEquiv.MulOfAdd _))
  apply congrLogHomToGroupHom
  apply GroupEquiv.of_log_exp g (ExpEquiv.MulOfAdd _)
  apply ExpEquiv.add_trans h (ExpEquiv.MulOfAdd _)

def congrExpHom (h: α ≃+ γ) (g: β ≃* δ) : (α →ₐ* β) ≃ (γ →ₐ* δ) where
  toFun f := (ExpHom.comp_mul g.toHom f).add_comp h.symm.toHom
  invFun f := (ExpHom.comp_mul g.symm.toHom f).add_comp h.toHom
  leftInv _ := by ext; simp
  rightInv _ := by ext; simp

def congrLogHom (h: α ≃* γ) (g: β ≃+ δ) : (α →ₘ+ β) ≃ (γ →ₘ+ δ) where
  toFun f := (LogHom.comp_add g.toHom f).mul_comp h.symm.toHom
  invFun f := (LogHom.comp_add g.symm.toHom f).mul_comp h.toHom
  leftInv _ := by ext; simp
  rightInv _ := by ext; simp

def congrGroupHom (h: α ≃* γ) (g: β ≃* δ) : (α →* β) ≃ (γ →* δ) where
  toFun f := (g.toHom.comp f).comp h.symm.toHom
  invFun f := (g.symm.toHom.comp f).comp h.toHom
  leftInv _ := by ext; simp
  rightInv _ := by ext; simp

def congrAddGroupHom (h: α ≃* γ) (g: β ≃* δ) : (α →* β) ≃ (γ →* δ) where
  toFun f := (g.toHom.comp f).comp h.symm.toHom
  invFun f := (g.symm.toHom.comp f).comp h.toHom
  leftInv _ := by ext; simp
  rightInv _ := by ext; simp

def exp_hom_equiv_addgroup_hom : (α →ₐ* β) ≃ (α →+ AddOfMul β) := congrExpHomToAddGroupHom .refl (.AddOfMul _)
def exp_hom_equiv_group_hom : (α →ₐ* β) ≃ (MulOfAdd α →* β) := congrExpHomToGroupHom (.MulOfAdd _) .refl
def log_hom_equiv_group_hom : (α →ₘ+ β) ≃ (α →* MulOfAdd β) := congrLogHomToGroupHom .refl (.MulOfAdd _)
def log_hom_equiv_addgroup_hom : (α →ₘ+ β) ≃ (AddOfMul α →+ β) := congrLogHomToAddGroupHom (.AddOfMul _) .refl

def group_hom_eqv_exp_hom : (α →* β) ≃ (AddOfMul α →ₐ* β) := (congrExpHomToGroupHom (.AddOfMul _) .refl).symm
def addgroup_hom_eqv_exp_hom : (α →+ β) ≃ (α →ₐ* MulOfAdd β) := (congrExpHomToAddGroupHom .refl (.MulOfAdd _)).symm
def group_hom_eqv_log_hom : (α →* β) ≃ (α →ₘ+ AddOfMul β) := (congrLogHomToGroupHom .refl (.AddOfMul _)).symm
def addgroup_hom_eqv_log_hom : (α →+ β) ≃ (MulOfAdd α →ₘ+ β) := (congrLogHomToAddGroupHom (.MulOfAdd _) .refl).symm

end Equiv
