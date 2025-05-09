import Math.Algebra.SetLike

variable (S: Type*) {α: Type*} [SetLike S α]

namespace Subsemigroup

variable [Mul α]

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

@[ext]
def ext (a b: AddSubsemigroup α) : (∀x, x ∈ a ↔ x ∈ b) -> a = b := SetLike.ext _ _

inductive Generate (U: Set α) : α -> Prop where
| of (a: α) : a ∈ U -> Generate U a
| add {a b: α} : Generate U a -> Generate U b -> Generate U (a + b)

def generate (U: Set α) : AddSubsemigroup α where
  carrier := Set.mk (Generate U)
  mem_add := Generate.add

end AddSubsemigroup
