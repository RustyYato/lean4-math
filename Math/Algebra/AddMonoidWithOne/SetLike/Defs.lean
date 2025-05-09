import Math.Algebra.Monoid.SetLike.Defs

variable (S: Type*) {α: Type*} [SetLike S α]

class IsAddSubmonoidWithOne [Add α] [Zero α] [One α] : Prop extends IsAddSubmonoid S, IsOneMem S where

structure AddSubmonoidWithOne (α: Type*) [Add α] [Zero α] [One α] extends AddSubmonoid α where
  mem_one : 1 ∈ carrier

namespace AddSubmonoidWithOne

variable [Add α] [Zero α] [One α]

instance : SetLike (AddSubmonoidWithOne α) α where
instance : IsAddSubmonoidWithOne (AddSubmonoidWithOne α) where

@[ext]
def ext (a b: AddSubmonoidWithOne α) : (∀x, x ∈ a ↔ x ∈ b) -> a = b := SetLike.ext _ _

inductive Generate (U: Set α) : α -> Prop where
| of (a: α) : a ∈ U -> Generate U a
| add {a b: α} : Generate U a -> Generate U b -> Generate U (a + b)
| zero : Generate U 0
| one : Generate U 1

def generate (U: Set α) : AddSubmonoidWithOne α where
  carrier := Set.mk (Generate U)
  mem_add := Generate.add
  mem_zero := Generate.zero
  mem_one := Generate.one

def copy (s: AddSubmonoidWithOne α) (U: Set α) (h: s = U) : AddSubmonoidWithOne α := {
  s.toAddSubmonoid.copy U h with
  mem_one := h ▸ mem_one s
}

end AddSubmonoidWithOne
