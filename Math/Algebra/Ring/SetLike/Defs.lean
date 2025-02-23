import Math.Algebra.Semiring.SetLike.Defs
import Math.Algebra.AddGroupWithOne.SetLike.Defs

variable (S: Type*) {α: Type*} [SetLike S α]

class IsSubring [Add α] [Mul α] [Neg α] [Zero α] [One α] extends IsSubSemiring S, IsAddSubgroupWithOne S: Prop where

structure Subring (α: Type*) [Add α] [Mul α] [Neg α] [Zero α] [One α] extends SubSemiring α, AddSubgroupWithOne α where

variable [Add α] [Mul α] [Neg α] [Zero α] [One α]

instance : SetLike (Subring α) α where
  coe a := a.carrier
  coe_inj := by
    intro a b eq; cases a; congr
    apply SetLike.coe_inj
    assumption

instance : IsSubring (Subring α) where
  mem_add a := a.mem_add'
  mem_mul a := a.mem_mul'
  mem_neg a := a.mem_neg'
  mem_zero a := a.mem_zero'
  mem_one a := a.mem_one'

@[ext]
def Subring.ext (a b: Subring α) : (∀x, x ∈ a ↔ x ∈ b) -> a = b := SetLike.ext _ _
