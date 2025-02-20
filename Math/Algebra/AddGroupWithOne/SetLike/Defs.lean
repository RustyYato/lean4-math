import Math.Algebra.AddMonoidWithOne.SetLike.Defs
import Math.Algebra.Group.SetLike.Defs

variable (S: Type*) {α: Type*} [SetLike S α]

class IsSubAddGroupWithOne [Add α] [Zero α] [Neg α] [One α] extends IsSubAddMonoidWithOne S, IsSubAddGroup S: Prop where

structure SubAddGroupWithOne (α: Type*) [Add α] [Neg α] [Zero α] [One α] extends SubAddMonoidWithOne α, SubAddGroup α where

variable [Add α] [Neg α] [Zero α] [One α]

instance : SetLike (SubAddGroupWithOne α) α where
  coe a := a.carrier
  coe_inj := by
    intro a b eq; cases a; congr
    apply SetLike.coe_inj
    assumption

instance : IsSubAddGroupWithOne (SubAddGroupWithOne α) where
  mem_add a := a.mem_add'
  mem_neg a := a.mem_neg'
  mem_zero a := a.mem_zero'
  mem_one a := a.mem_one'

@[ext]
def SubAddGroupWithOne.ext (a b: SubAddGroupWithOne α) : (∀x, x ∈ a ↔ x ∈ b) -> a = b := SetLike.ext _ _
