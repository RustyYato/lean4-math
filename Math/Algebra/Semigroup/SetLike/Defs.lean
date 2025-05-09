import Math.Algebra.SetLike.Defs

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

def of_mem_generate {S: Type*} [SetLike S α] [IsMulMem S] (U: Set α) (s: S) :
  (∀x ∈ U, x ∈ s) ->  ∀x ∈ generate U, x ∈ s := by
  intro h x hx
  show x ∈ s
  induction hx with
  | of =>
    apply h
    assumption
  | mul => apply mem_mul <;> assumption

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

def of_mem_generate {S: Type*} [SetLike S α] [IsAddMem S] (U: Set α) (s: S) :
  (∀x ∈ U, x ∈ s) -> ∀x ∈ generate U, x ∈ s := by
  intro h x hx
  show x ∈ s
  induction hx with
  | of =>
    apply h
    assumption
  | add => apply mem_add <;> assumption

end AddSubsemigroup
