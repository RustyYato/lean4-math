import Math.Algebra.Semigroup.SetLike.Defs
import Math.Algebra.Notation

variable (S: Type*) {α: Type*} [SetLike S α]

class IsOneMem [One α] : Prop where
  mem_one (s: S) : 1 ∈ s := by intro s; exact s.mem_one

def mem_one {S α: Type*} [SetLike S α] [One α] [IsOneMem S]
  (s: S) : 1 ∈ s := IsOneMem.mem_one s

class IsZeroMem [Zero α] : Prop where
  mem_zero (s: S) : 0 ∈ s := by intro s; exact s.mem_zero

def mem_zero {S α: Type*} [SetLike S α] [Zero α] [IsZeroMem S]
  (s: S) : 0 ∈ s := IsZeroMem.mem_zero s

class IsSubmonoid [Mul α] [One α] : Prop extends IsMulMem S, IsOneMem S where
class IsAddSubmonoid [Add α] [Zero α] : Prop extends IsAddMem S, IsZeroMem S where

structure Submonoid (α: Type*) [Mul α] [One α] extends Subsemigroup α where
  protected mem_one: 1 ∈ carrier

structure AddSubmonoid (α: Type*) [Add α] [Zero α] extends AddSubsemigroup α where
  protected mem_zero: 0 ∈ carrier

instance [SetLike S α] [Add α] [Zero α] [IsAddSubmonoid S] : IsSubmonoid (MulOfAdd S) where
  mem_one := mem_zero (S := S)
instance [SetLike S α] [Mul α] [One α] [IsSubmonoid S] : IsAddSubmonoid (AddOfMul S) where
  mem_zero := mem_one (S := S)

namespace Submonoid

variable [Mul α] [One α]

instance : SetLike (Submonoid α) α where
  coe a := a.carrier
  coe_inj := by
    intro a b eq; cases a; congr
    apply SetLike.coe_inj
    assumption

instance : IsSubmonoid (Submonoid α) where
  mem_mul a := a.mem_mul
  mem_one a := a.mem_one

@[ext]
def ext (a b: Submonoid α) : (∀x, x ∈ a ↔ x ∈ b) -> a = b := SetLike.ext _ _

inductive Generate (U: Set α) : α -> Prop where
| of (a: α) : a ∈ U -> Generate U a
| mul {a b: α} : Generate U a -> Generate U b -> Generate U (a * b)
| one : Generate U 1

def generate (U: Set α) : Submonoid α where
  carrier := Set.mk (Generate U)
  mem_mul := Generate.mul
  mem_one := Generate.one

end Submonoid

namespace AddSubmonoid

variable [Add α] [Zero α]

instance : SetLike (AddSubmonoid α) α where
  coe a := a.carrier
  coe_inj := by
    intro a b eq; cases a; congr
    apply SetLike.coe_inj
    assumption

instance : IsAddSubmonoid (AddSubmonoid α) where
  mem_add a := a.mem_add
  mem_zero a := a.mem_zero

@[ext]
def ext (a b: AddSubmonoid α) : (∀x, x ∈ a ↔ x ∈ b) -> a = b := SetLike.ext _ _

inductive Generate (U: Set α) : α -> Prop where
| of (a: α) : a ∈ U -> Generate U a
| add {a b: α} : Generate U a -> Generate U b -> Generate U (a + b)
| zero : Generate U 0

def generate (U: Set α) : AddSubmonoid α where
  carrier := Set.mk (Generate U)
  mem_add := Generate.add
  mem_zero := Generate.zero

end AddSubmonoid
