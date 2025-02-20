import Math.Algebra.Monoid.SetLike.Defs

variable (S: Type*) {α: Type*} [SetLike S α]

class IsSubAddMonoidWithOne [Add α] [Zero α] [One α] extends IsSubAddMonoid S, IsOneMem S: Prop where

structure SubAddMonoidWithOne (α: Type*) [Add α] [Zero α] [One α] extends SubAddMonoid α where
  mem_one' : 1 ∈ carrier

variable [Add α] [Zero α] [One α]

instance : SetLike (SubAddMonoidWithOne α) α where
  coe a := a.carrier
  coe_inj := by
    intro a b eq; cases a; congr
    apply SetLike.coe_inj
    assumption

instance : IsSubAddMonoidWithOne (SubAddMonoidWithOne α) where
  mem_add a := a.mem_add'
  mem_zero a := a.mem_zero'
  mem_one a := a.mem_one'

@[ext]
def SubAddMonoidWithOne.ext (a b: SubAddMonoidWithOne α) : (∀x, x ∈ a ↔ x ∈ b) -> a = b := SetLike.ext _ _
