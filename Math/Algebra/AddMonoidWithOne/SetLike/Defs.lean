import Math.Algebra.Monoid.SetLike.Defs

variable (S: Type*) {α: Type*} [SetLike S α]

class IsAddSubmonoidWithOne [Add α] [Zero α] [One α] extends IsAddSubmonoid S, IsOneMem S: Prop where

structure AddSubmonoidWithOne (α: Type*) [Add α] [Zero α] [One α] extends AddSubmonoid α where
  mem_one' : 1 ∈ carrier

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
def AddSubmonoidWithOne.ext (a b: AddSubmonoidWithOne α) : (∀x, x ∈ a ↔ x ∈ b) -> a = b := SetLike.ext _ _
