import Math.Algebra.Ring.SetLike.Defs
import Math.Order.Atom.Basic
import Math.Algebra.Ring.Defs

section

variable (S: Type*) {α: Type*} [SetLike S α]

class IsMemMulLeft [Mul α]: Prop where
  mem_mul_left (s: S): ∀(r: α) (x: α), x ∈ s -> r * x ∈ s

def mem_mul_left {S α: Type*} [SetLike S α] [Mul α] [IsMemMulLeft S] (s: S): ∀(r: α) (x: α), x ∈ s -> r * x ∈ s :=
  IsMemMulLeft.mem_mul_left s

class IsMemMulRight [Mul α]: Prop where
  mem_mul_right (s: S): ∀(r: α) (x: α), x ∈ s -> x * r ∈ s

def mem_mul_right {S α: Type*} [SetLike S α] [Mul α] [IsMemMulRight S] (s: S): ∀(r: α) (x: α), x ∈ s -> x * r ∈ s :=
  IsMemMulRight.mem_mul_right s

class IsLeftIdeal [Add α] [Mul α] [Neg α] [Zero α] : Prop extends IsAddSubgroup S, IsMemMulLeft S where
class IsRightIdeal [Add α] [Mul α] [Neg α] [Zero α] : Prop extends IsAddSubgroup S, IsMemMulRight S where
class IsIdeal [Add α] [Mul α] [Neg α] [Zero α] : Prop extends IsLeftIdeal S, IsRightIdeal S where

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

structure LeftIdeal extends AddSubgroup α where
  protected mem_mul_left: ∀(r: α) {x}, x ∈ carrier -> r * x ∈ carrier

structure RightIdeal extends AddSubgroup α where
  protected mem_mul_right: ∀(r: α) {x}, x ∈ carrier -> x * r ∈ carrier

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

instance : IsAddSubgroup (LeftIdeal α) where
  mem_add i := i.mem_add
  mem_neg i := i.mem_neg
  mem_zero i := i.mem_zero

instance : IsAddSubgroup (RightIdeal α) where
  mem_add i := i.mem_add
  mem_neg i := i.mem_neg
  mem_zero i := i.mem_zero

instance : IsAddSubgroup (Ideal α) where
  mem_add i := i.mem_add
  mem_neg i := i.mem_neg
  mem_zero i := i.mem_zero

instance : IsIdeal (Ideal α) where
  mem_mul_left i := i.mem_mul_left
  mem_mul_right i := i.mem_mul_right

instance : IsLeftIdeal (LeftIdeal α) where
  mem_mul_left i := i.mem_mul_left

instance : IsRightIdeal (RightIdeal α) where
  mem_mul_right i := i.mem_mul_right

instance : IsMulMem (LeftIdeal α) := inferInstance
instance : IsMulMem (RightIdeal α) := inferInstance
instance : IsMulMem (Ideal α) := inferInstance

end

namespace Ideal

def zero (α: Type*) [AddGroupOps α] [Mul α] [IsAddGroup α] [IsMulZeroClass α] : Ideal α where
  carrier := {0}
  mem_zero := rfl
  mem_add := by
    rintro _ _ rfl rfl
    apply add_zero
  mem_neg := by
    rintro _ rfl
    apply neg_zero
  mem_mul_left := by
    rintro r _ rfl
    apply mul_zero
  mem_mul_right := by
    rintro r _ rfl
    apply zero_mul

def univ (α: Type*) [Add α] [Mul α] [Neg α] [Zero α] : Ideal α where
  carrier := ⊤
  mem_zero := True.intro
  mem_add _ _ := True.intro
  mem_neg _ := True.intro
  mem_mul_left _ _ _ := True.intro
  mem_mul_right _ _ _ := True.intro

instance [AddGroupOps α] [Mul α] [IsAddGroup α] [IsMulZeroClass α] : Zero (Ideal α) := ⟨Ideal.zero α⟩

instance [Add α] [Mul α] [Neg α] [Zero α] : One (Ideal α) where
  one := .univ α

end Ideal

variable {α: Type*} [Add α] [Mul α] [Neg α] [Zero α]

namespace Ideal

inductive Generate (U: Set α) : α -> Prop where
| of (x: α) : x ∈ U -> Generate U x
| zero : Generate U 0
| add {a b: α} : Generate U a -> Generate U b -> Generate U (a + b)
| neg {a: α} : Generate U a -> Generate U (-a)
| mul_left (r: α) {x: α} : Generate U x -> Generate U (r * x)
| mul_right (r: α) {x: α} : Generate U x -> Generate U (x * r)

def generate (U: Set α) : Ideal α where
  carrier := Set.mk (Generate U)
  mem_zero := Generate.zero
  mem_add := Generate.add
  mem_neg := Generate.neg
  mem_mul_left := Generate.mul_left
  mem_mul_right := Generate.mul_right

def of_mem_generate [SetLike S α] [IsIdeal S] (U: Set α) (s: S) :
  (∀x ∈ U, x ∈ s) -> (generate U).carrier ⊆ s := by
  intro g
  intro x h
  show x ∈ s
  induction h with
  | of =>
    apply g
    assumption
  | zero =>
    apply mem_zero
  | neg =>
    apply mem_neg
    assumption
  | add =>
    apply mem_add
    assumption
    assumption
  | mul_left =>
    apply mem_mul_left
    assumption
  | mul_right =>
    apply mem_mul_right
    assumption

@[ext]
def ext {a b: Ideal α} : (∀x, x ∈ a ↔ x ∈ b) -> a = b := SetLike.ext _ _

end Ideal

namespace LeftIdeal

inductive Generate (U: Set α) : α -> Prop where
| of (x: α) : x ∈ U -> Generate U x
| zero : Generate U 0
| add {a b: α} : Generate U a -> Generate U b -> Generate U (a + b)
| neg {a: α} : Generate U a -> Generate U (-a)
| mul_left (r: α) {x: α} : Generate U x -> Generate U (r * x)

def generate (U: Set α) : LeftIdeal α where
  carrier := Set.mk (Generate U)
  mem_zero := Generate.zero
  mem_add := Generate.add
  mem_neg := Generate.neg
  mem_mul_left := Generate.mul_left

@[ext]
def ext {a b: LeftIdeal α} : (∀x, x ∈ a ↔ x ∈ b) -> a = b := SetLike.ext _ _

end LeftIdeal

namespace RightIdeal

inductive Generate (U: Set α) : α -> Prop where
| of (x: α) : x ∈ U -> Generate U x
| zero : Generate U 0
| add {a b: α} : Generate U a -> Generate U b -> Generate U (a + b)
| neg {a: α} : Generate U a -> Generate U (-a)
| mul_right (r: α) {x: α} : Generate U x -> Generate U (x * r)

def generate (U: Set α) : RightIdeal α where
  carrier := Set.mk (Generate U)
  mem_zero := Generate.zero
  mem_add := Generate.add
  mem_neg := Generate.neg
  mem_mul_right := Generate.mul_right

@[ext]
def ext {a b: RightIdeal α} : (∀x, x ∈ a ↔ x ∈ b) -> a = b := SetLike.ext _ _

end RightIdeal
