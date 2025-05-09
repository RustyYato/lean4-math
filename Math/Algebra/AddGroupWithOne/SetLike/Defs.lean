import Math.Algebra.AddMonoidWithOne.SetLike.Defs
import Math.Algebra.Group.SetLike.Defs

variable (S: Type*) {α: Type*} [SetLike S α]

class IsAddSubgroupWithOne [Add α] [Zero α] [Neg α] [One α] : Prop extends IsAddSubmonoidWithOne S, IsAddSubgroup S where

structure AddSubgroupWithOne (α: Type*) [Add α] [Neg α] [Zero α] [One α] extends AddSubmonoidWithOne α, AddSubgroup α where

namespace AddSubgroupWithOne

variable [Add α] [Neg α] [Zero α] [One α]

instance : SetLike (AddSubgroupWithOne α) α where
instance : IsAddSubgroupWithOne (AddSubgroupWithOne α) where

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

def of_mem_generate {S: Type*} [SetLike S α] [IsAddSubgroupWithOne S] (U: Set α) (s: S) :
  (∀x ∈ U, x ∈ s) -> ∀x ∈ generate U, x ∈ s := by
  intro h x hx
  show x ∈ s
  induction hx with
  | of =>
    apply h
    assumption
  | zero => apply mem_zero <;> assumption
  | one => apply mem_one <;> assumption
  | neg => apply mem_neg <;> assumption
  | add => apply mem_add <;> assumption

def copy (s: AddSubgroupWithOne α) (U: Set α) (h: s = U) : AddSubgroupWithOne α := {
  s.toAddSubmonoidWithOne.copy U h, s.toAddSubgroup.copy U h with
}

end AddSubgroupWithOne
