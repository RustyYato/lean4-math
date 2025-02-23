import Math.Algebra.AddMonoidWithOne.SetLike.Defs
import Math.Algebra.Group.SetLike.Defs

variable (S: Type*) {α: Type*} [SetLike S α]

class IsAddSubgroupWithOne [Add α] [Zero α] [Neg α] [One α] extends IsAddSubmonoidWithOne S, IsAddSubGroup S: Prop where

structure AddSubgroupWithOne (α: Type*) [Add α] [Neg α] [Zero α] [One α] extends AddSubmonoidWithOne α, AddSubGroup α where

variable [Add α] [Neg α] [Zero α] [One α]

instance : SetLike (AddSubgroupWithOne α) α where
  coe a := a.carrier
  coe_inj := by
    intro a b eq; cases a; congr
    apply SetLike.coe_inj
    assumption

instance : IsAddSubgroupWithOne (AddSubgroupWithOne α) where
  mem_add a := a.mem_add'
  mem_neg a := a.mem_neg'
  mem_zero a := a.mem_zero'
  mem_one a := a.mem_one'

@[ext]
def AddSubgroupWithOne.ext (a b: AddSubgroupWithOne α) : (∀x, x ∈ a ↔ x ∈ b) -> a = b := SetLike.ext _ _
