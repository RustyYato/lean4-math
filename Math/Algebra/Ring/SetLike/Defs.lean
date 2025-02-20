import Math.Algebra.Semiring.SetLike.Defs
import Math.Algebra.AddGroupWithOne.SetLike.Defs

variable (S: Type*) {α: Type*} [SetLike S α]

class IsSubRing [Add α] [Mul α] [Neg α] [Zero α] [One α] extends IsSubSemiring S, IsSubAddGroupWithOne S: Prop where

structure SubRing (α: Type*) [Add α] [Mul α] [Neg α] [Zero α] [One α] extends SubSemiring α, SubAddGroupWithOne α where

variable [Add α] [Mul α] [Neg α] [Zero α] [One α]

instance : SetLike (SubRing α) α where
  coe a := a.carrier
  coe_inj := by
    intro a b eq; cases a; congr
    apply SetLike.coe_inj
    assumption

instance : IsSubRing (SubRing α) where
  mem_add a := a.mem_add'
  mem_mul a := a.mem_mul'
  mem_neg a := a.mem_neg'
  mem_zero a := a.mem_zero'
  mem_one a := a.mem_one'

@[ext]
def SubRing.ext (a b: SubRing α) : (∀x, x ∈ a ↔ x ∈ b) -> a = b := SetLike.ext _ _
