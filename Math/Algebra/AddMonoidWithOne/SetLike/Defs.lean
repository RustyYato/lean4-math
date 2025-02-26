import Math.Algebra.Monoid.SetLike.Defs

variable (S: Type*) {α: Type*} [SetLike S α]

class IsAddSubmonoidWithOne [Add α] [Zero α] [One α] : Prop extends IsAddSubmonoid S, IsOneMem S where

structure AddSubmonoidWithOne (α: Type*) [Add α] [Zero α] [One α] extends AddSubmonoid α where
  mem_one' : 1 ∈ carrier

namespace AddSubmonoidWithOne

variable [Add α] [Zero α] [One α]

instance : SetLike (AddSubmonoidWithOne α) α where
  coe a := a.carrier
  coe_inj := by
    intro a b eq; cases a; congr
    apply SetLike.coe_inj
    assumption

instance : IsAddSubmonoidWithOne (AddSubmonoidWithOne α) where
  mem_add a := a.mem_add'
  mem_zero a := a.mem_zero'
  mem_one a := a.mem_one'

@[ext]
def ext (a b: AddSubmonoidWithOne α) : (∀x, x ∈ a ↔ x ∈ b) -> a = b := SetLike.ext _ _

inductive Generate (U: Set α) : α -> Prop where
| of (a: α) : a ∈ U -> Generate U a
| add {a b: α} : Generate U a -> Generate U b -> Generate U (a + b)
| zero : Generate U 0
| one : Generate U 1

def generate (U: Set α) : AddSubmonoidWithOne α where
  carrier := Set.mk (Generate U)
  mem_add' := Generate.add
  mem_zero' := Generate.zero
  mem_one' := Generate.one

end AddSubmonoidWithOne
