import Math.Algebra.AddMonoidWithOne.SetLike.Defs
import Math.Algebra.Group.SetLike.Defs

variable (S: Type*) {α: Type*} [SetLike S α]

class IsAddSubgroupWithOne [Add α] [Zero α] [Neg α] [One α] : Prop extends IsAddSubmonoidWithOne S, IsAddSubgroup S where

structure AddSubgroupWithOne (α: Type*) [Add α] [Neg α] [Zero α] [One α] extends AddSubmonoidWithOne α, AddSubgroup α where

namespace AddSubgroupWithOne

variable [Add α] [Neg α] [Zero α] [One α]

instance : SetLike (AddSubgroupWithOne α) α where
  coe a := a.carrier
  coe_inj := by
    intro a b eq; cases a; congr
    apply SetLike.coe_inj
    assumption

instance : IsAddSubgroupWithOne (AddSubgroupWithOne α) where
  mem_add a := a.mem_add
  mem_neg a := a.mem_neg
  mem_zero a := a.mem_zero
  mem_one a := a.mem_one

@[ext]
def ext (a b: AddSubgroupWithOne α) : (∀x, x ∈ a ↔ x ∈ b) -> a = b := SetLike.ext _ _

inductive Generate (U: Set α) : α -> Prop where
| of (a: α) : a ∈ U -> Generate U a
| add {a b: α} : Generate U a -> Generate U b -> Generate U (a + b)
| neg {a: α} : Generate U a -> Generate U (-a)
| zero : Generate U 0
| one : Generate U 1

def generate (U: Set α) : AddSubgroupWithOne α where
  carrier := Set.mk (Generate U)
  mem_add := Generate.add
  mem_neg := Generate.neg
  mem_zero := Generate.zero
  mem_one := Generate.one

end AddSubgroupWithOne
