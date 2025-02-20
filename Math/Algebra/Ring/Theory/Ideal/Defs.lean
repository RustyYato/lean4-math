import Math.Algebra.Ring.SetLike.Defs
import Math.Order.Atom.Basic
import Math.Algebra.Ring.Defs

section

variable (S: Type*) {α: Type*} [SetLike S α]

class IsMemMulLeft [Mul α]: Prop where
  mem_mul_left (s: S): ∀(r: α) (x: α), x ∈ s -> r * x ∈ s

def mem_mul_left [Mul α] [IsMemMulLeft S] (s: S): ∀(r: α) (x: α), x ∈ s -> r * x ∈ s :=
  IsMemMulLeft.mem_mul_left s

class IsMemMulRight [Mul α]: Prop where
  mem_mul_right (s: S): ∀(r: α) (x: α), x ∈ s -> x * r ∈ s

def mem_mul_right [Mul α] [IsMemMulRight S] (s: S): ∀(r: α) (x: α), x ∈ s -> x * r ∈ s :=
  IsMemMulRight.mem_mul_right s

class IsLeftIdeal [Add α] [Mul α] [Neg α] [Zero α] extends IsSubAddGroup S, IsMemMulLeft S: Prop where
class IsRightIdeal [Add α] [Mul α] [Neg α] [Zero α] extends IsSubAddGroup S, IsMemMulRight S: Prop where
class IsIdeal [Add α] [Mul α] [Neg α] [Zero α] extends IsLeftIdeal S, IsRightIdeal S: Prop where

instance [Mul α] [IsMemMulLeft S] : IsMulMem S where
  mem_mul := by
    intros
    apply mem_mul_left
    assumption
instance [Mul α] [IsMemMulRight S] : IsMulMem S where
  mem_mul := by
    intros
    apply mem_mul_right
    assumption

end

section

variable (α: Type*) [Add α] [Mul α] [Neg α] [Zero α]

structure LeftIdeal extends SubAddGroup α where
  mem_mul_left': ∀(r: α) {x}, x ∈ carrier -> r * x ∈ carrier

structure RightIdeal extends SubAddGroup α where
  mem_mul_right': ∀(r: α) {x}, x ∈ carrier -> x * r ∈ carrier

structure Ideal extends LeftIdeal α, RightIdeal α where

instance : SetLike (LeftIdeal α) α where
  coe a := a.carrier
  coe_inj := by
    intro a b eq; cases a; congr
    apply SetLike.coe_inj
    assumption

instance : SetLike (RightIdeal α) α where
  coe a := a.carrier
  coe_inj := by
    intro a b eq; cases a; congr
    apply SetLike.coe_inj
    assumption

instance : SetLike (Ideal α) α where
  coe a := a.carrier
  coe_inj := by
    intro a b eq; cases a; congr
    apply SetLike.coe_inj
    assumption

instance : IsSubAddGroup (LeftIdeal α) where
  mem_add i := i.mem_add'
  mem_neg i := i.mem_neg'
  mem_zero i := i.mem_zero'

instance : IsSubAddGroup (RightIdeal α) where
  mem_add i := i.mem_add'
  mem_neg i := i.mem_neg'
  mem_zero i := i.mem_zero'

instance : IsSubAddGroup (Ideal α) where
  mem_add i := i.mem_add'
  mem_neg i := i.mem_neg'
  mem_zero i := i.mem_zero'

instance : IsIdeal (Ideal α) where
  mem_mul_left i := i.mem_mul_left'
  mem_mul_right i := i.mem_mul_right'

instance : IsLeftIdeal (LeftIdeal α) where
  mem_mul_left i := i.mem_mul_left'

instance : IsRightIdeal (RightIdeal α) where
  mem_mul_right i := i.mem_mul_right'

instance : IsMulMem (LeftIdeal α) := inferInstance
instance : IsMulMem (RightIdeal α) := inferInstance
instance : IsMulMem (Ideal α) := inferInstance

end

def Ideal.zero (α: Type*) [AddGroupOps α] [Mul α] [IsAddGroup α] [IsMulZeroClass α] : Ideal α where
  carrier := {0}
  mem_zero' := rfl
  mem_add' := by
    rintro _ _ rfl rfl
    apply add_zero
  mem_neg' := by
    rintro _ rfl
    apply neg_zero
  mem_mul_left' := by
    rintro r _ rfl
    apply mul_zero
  mem_mul_right' := by
    rintro r _ rfl
    apply zero_mul

def Ideal.univ (α: Type*) [Add α] [Mul α] [Neg α] [Zero α] : Ideal α where
  carrier := ⊤
  mem_zero' := True.intro
  mem_add' _ _ := True.intro
  mem_neg' _ := True.intro
  mem_mul_left' _ _ _ := True.intro
  mem_mul_right' _ _ _ := True.intro

variable {α: Type*} [Add α] [Mul α] [Neg α] [Zero α]

@[ext]
def LeftIdeal.ext {a b: LeftIdeal α} : (∀x, x ∈ a ↔ x ∈ b) -> a = b := SetLike.ext _ _

@[ext]
def RightIdeal.ext {a b: RightIdeal α} : (∀x, x ∈ a ↔ x ∈ b) -> a = b := SetLike.ext _ _

@[ext]
def Ideal.ext {a b: Ideal α} : (∀x, x ∈ a ↔ x ∈ b) -> a = b := SetLike.ext _ _
