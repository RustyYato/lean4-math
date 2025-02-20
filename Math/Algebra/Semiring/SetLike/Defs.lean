import Math.Algebra.AddMonoidWithOne.SetLike.Defs

variable (S: Type*) {α: Type*} [SetLike S α]

class IsSubSemiring [Add α] [Mul α] [Zero α] [One α] extends IsSubAddMonoidWithOne S, IsSubMonoid S: Prop where

structure SubSemiring (α: Type*) [Add α] [Mul α] [Zero α] [One α] extends SubAddMonoidWithOne α, SubMonoid α where

variable [Add α] [Mul α] [Zero α] [One α]

instance : SetLike (SubSemiring α) α where
  coe a := a.carrier
  coe_inj := by
    intro a b eq; cases a; congr
    apply SetLike.coe_inj
    assumption

instance : IsSubSemiring (SubSemiring α) where
  mem_add a := a.mem_add'
  mem_mul a := a.mem_mul'
  mem_zero a := a.mem_zero'
  mem_one a := a.mem_one'

@[ext]
def SubSemiring.ext (a b: SubSemiring α) : (∀x, x ∈ a ↔ x ∈ b) -> a = b := SetLike.ext _ _
