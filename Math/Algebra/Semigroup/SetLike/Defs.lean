import Math.Data.Set.Like
import Math.Algebra.AddMul

variable (S: Type*) {α: Type*} [SetLike S α]

class IsMulMem [Mul α] : Prop where
  mem_mul (s: S) {a b: α} : a ∈ s -> b ∈ s -> a * b ∈ s

def mem_mul {S α: Type*} [SetLike S α] [Mul α] [IsMulMem S]
  (s: S) {a b: α} : a ∈ s -> b ∈ s -> a * b ∈ s := IsMulMem.mem_mul s

class IsAddMem [Add α] : Prop where
  mem_add (s: S) {a b: α} : a ∈ s -> b ∈ s -> a + b ∈ s

def mem_add {S α: Type*} [SetLike S α] [Add α] [IsAddMem S]
  (s: S) {a b: α} : a ∈ s -> b ∈ s -> a + b ∈ s := IsAddMem.mem_add s

structure Subsemigroup (α: Type*) [Mul α] where
  carrier: Set α
  protected mem_mul {a b: α} : a ∈ carrier -> b ∈ carrier -> a * b ∈ carrier

structure AddSubsemigroup (α: Type*) [Add α] where
  carrier: Set α
  protected mem_add {a b: α} : a ∈ carrier -> b ∈ carrier -> a + b ∈ carrier

instance [h: SetLike S α] : SetLike (AddOfMul S) (AddOfMul α) where
  coe a := (a.get: Set α)
  coe_inj := h.coe_inj
instance [h: SetLike S α] : SetLike (MulOfAdd S) (MulOfAdd α) where
  coe a := (a.get: Set α)
  coe_inj := h.coe_inj

instance [SetLike S α] [Add α] [IsAddMem S] : IsMulMem (MulOfAdd S) where
  mem_mul := mem_add (S := S)
instance [SetLike S α] [Mul α] [IsMulMem S] : IsAddMem (AddOfMul S) where
  mem_add := mem_mul (S := S)

namespace Subsemigroup

variable [Mul α]

instance : SetLike (Subsemigroup α) α where
  coe := Subsemigroup.carrier
  coe_inj := by
    intro a b eq; cases a; congr

instance : IsMulMem (Subsemigroup α) where
  mem_mul := Subsemigroup.mem_mul

@[ext]
def ext (a b: Subsemigroup α) : (∀x, x ∈ a ↔ x ∈ b) -> a = b := SetLike.ext _ _

inductive Generate (U: Set α) : α -> Prop where
| of (a: α) : a ∈ U -> Generate U a
| mul {a b: α} : Generate U a -> Generate U b -> Generate U (a * b)

def generate (U: Set α) : Subsemigroup α where
  carrier := Set.mk (Generate U)
  mem_mul := Generate.mul

end Subsemigroup

namespace AddSubsemigroup

variable [Add α]

instance : SetLike (AddSubsemigroup α) α where
  coe := AddSubsemigroup.carrier
  coe_inj := by
    intro a b eq; cases a; congr

instance : IsAddMem (AddSubsemigroup α) where
  mem_add := AddSubsemigroup.mem_add

@[ext]
def ext (a b: AddSubsemigroup α) : (∀x, x ∈ a ↔ x ∈ b) -> a = b := SetLike.ext _ _

inductive Generate (U: Set α) : α -> Prop where
| of (a: α) : a ∈ U -> Generate U a
| add {a b: α} : Generate U a -> Generate U b -> Generate U (a + b)

def generate (U: Set α) : AddSubsemigroup α where
  carrier := Set.mk (Generate U)
  mem_add := Generate.add

end AddSubsemigroup
