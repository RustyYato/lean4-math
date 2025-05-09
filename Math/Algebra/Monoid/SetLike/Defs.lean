import Math.Algebra.Semigroup.SetLike.Defs
import Math.Algebra.Notation

variable (S: Type*) {α: Type*} [SetLike S α]

class IsSubmonoid [Mul α] [One α] : Prop extends IsMulMem S, IsOneMem S where
class IsAddSubmonoid [Add α] [Zero α] : Prop extends IsAddMem S, IsZeroMem S where

structure Submonoid (α: Type*) [Mul α] [One α] extends Subsemigroup α, SubOne α where

structure AddSubmonoid (α: Type*) [Add α] [Zero α] extends AddSubsemigroup α, SubZero α where

instance [SetLike S α] [Add α] [Zero α] [IsAddSubmonoid S] : IsSubmonoid (MulOfAdd S) where
  mem_one := mem_zero (S := S)
instance [SetLike S α] [Mul α] [One α] [IsSubmonoid S] : IsAddSubmonoid (AddOfMul S) where
  mem_zero := mem_one (S := S)

namespace Submonoid

variable [Mul α] [One α]

instance : SetLike (Submonoid α) α where
instance : IsSubmonoid (Submonoid α) where

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

def copy (s: Submonoid α) (U: Set α) (h: s = U) : Submonoid α := {
  s.toSubsemigroup.copy U h, s.toSubOne.copy U h with
}

end Submonoid

namespace AddSubmonoid

variable [Add α] [Zero α]

instance : SetLike (AddSubmonoid α) α where
instance : IsAddSubmonoid (AddSubmonoid α) where

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

def copy (s: AddSubmonoid α) (U: Set α) (h: s = U) : AddSubmonoid α := {
  s.toAddSubsemigroup.copy U h, s.toSubZero.copy U h with
}

end AddSubmonoid
