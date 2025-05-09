import Math.Algebra.Monoid.SetLike.Defs
import Math.Algebra.Notation

variable (S: Type*) {α: Type*} [SetLike S α]

class IsInvMem [Inv α] : Prop where
  mem_inv (s: S) {a: α} (h: a ∈ s) : a⁻¹ ∈ s := by intro s; exact s.mem_inv

def mem_inv {S α: Type*} [SetLike S α] [Inv α] [IsInvMem S] (s: S) {a: α} (h: a ∈ s) : a⁻¹ ∈ s := IsInvMem.mem_inv s h

class IsNegMem [Neg α] : Prop where
  mem_neg (s: S) {a: α} (h: a ∈ s) : -a ∈ s := by intro s; exact s.mem_neg

def mem_neg {S α: Type*} [SetLike S α] [Neg α] [IsNegMem S] (s: S) {a: α} (h: a ∈ s) : -a ∈ s := IsNegMem.mem_neg s h

class IsSubgroup [Mul α] [One α] [Inv α] : Prop extends IsSubmonoid S, IsInvMem S where
class IsAddSubgroup [Add α] [Zero α] [Neg α] : Prop extends IsAddSubmonoid S, IsNegMem S where

structure Subgroup (α: Type*) [Mul α] [One α] [Inv α] extends Submonoid α where
  protected mem_inv: ∀{a}, a ∈ carrier -> a⁻¹ ∈ carrier

structure AddSubgroup (α: Type*) [Add α] [Zero α] [Neg α] extends AddSubmonoid α where
  protected mem_neg: ∀{a}, a ∈ carrier -> -a ∈ carrier

instance [SetLike S α] [Add α] [Zero α] [Neg α] [IsAddSubgroup S] : IsSubgroup (MulOfAdd S) where
  mem_inv := mem_neg (S := S)
instance [SetLike S α] [Mul α] [One α] [Inv α] [IsSubgroup S] : IsAddSubgroup (AddOfMul S) where
  mem_neg := mem_inv (S := S)

namespace Subgroup

variable [Mul α] [Inv α] [One α]

instance : SetLike (Subgroup α) α where
instance : IsSubgroup (Subgroup α) where

@[ext]
def ext [Mul α] [Inv α] [One α] (a b: Subgroup α) : (∀x, x ∈ a ↔ x ∈ b) -> a = b := SetLike.ext _ _

inductive Generate (U: Set α) : α -> Prop where
| of (a: α) : a ∈ U -> Generate U a
| mul {a b: α} : Generate U a -> Generate U b -> Generate U (a * b)
| inv {a: α} : Generate U a -> Generate U (a⁻¹)
| one : Generate U 1

def generate (U: Set α) : Subgroup α where
  carrier := Set.mk (Generate U)
  mem_mul := Generate.mul
  mem_one := Generate.one
  mem_inv := Generate.inv

def copy (s: Subgroup α) (U: Set α) (h: s = U) : Subgroup α := {
  s.toSubmonoid.copy U h with
  mem_inv := h ▸ mem_inv s
}

end Subgroup

namespace AddSubgroup

variable [Add α] [Neg α] [Zero α]

instance : SetLike (AddSubgroup α) α where
instance : IsAddSubgroup (AddSubgroup α) where

@[ext]
def ext [Add α] [Neg α] [Zero α] (a b: AddSubgroup α) : (∀x, x ∈ a ↔ x ∈ b) -> a = b := SetLike.ext _ _

inductive Generate (U: Set α) : α -> Prop where
| of (a: α) : a ∈ U -> Generate U a
| add {a b: α} : Generate U a -> Generate U b -> Generate U (a + b)
| neg {a: α} : Generate U a -> Generate U (-a)
| zero : Generate U 0

def generate (U: Set α) : AddSubgroup α where
  carrier := Set.mk (Generate U)
  mem_add := Generate.add
  mem_zero := Generate.zero
  mem_neg := Generate.neg

def copy (s: AddSubgroup α) (U: Set α) (h: s = U) : AddSubgroup α := {
  s.toAddSubmonoid.copy U h with
  mem_neg := h ▸ mem_neg s
}

end AddSubgroup
