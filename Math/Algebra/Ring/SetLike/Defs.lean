import Math.Algebra.Semiring.SetLike.Defs
import Math.Algebra.AddGroupWithOne.SetLike.Defs

variable (S: Type*) {α: Type*} [SetLike S α]

class IsSubring [Add α] [Mul α] [Neg α] [Zero α] [One α] : Prop extends IsSubsemiring S, IsAddSubgroupWithOne S where

structure Subring (α: Type*) [Add α] [Mul α] [Neg α] [Zero α] [One α] extends Subsemiring α, AddSubgroupWithOne α where

namespace Subring

variable [Add α] [Mul α] [Neg α] [Zero α] [One α]

instance : SetLike (Subring α) α where
  coe a := a.carrier
  coe_inj := by
    intro a b eq; cases a; congr
    apply SetLike.coe_inj
    assumption

instance : IsSubring (Subring α) where
  mem_add a := a.mem_add
  mem_mul a := a.mem_mul
  mem_neg a := a.mem_neg
  mem_zero a := a.mem_zero
  mem_one a := a.mem_one

@[ext]
def ext (a b: Subring α) : (∀x, x ∈ a ↔ x ∈ b) -> a = b := SetLike.ext _ _

inductive Generate (U: Set α) : α -> Prop where
| of (a: α) : a ∈ U -> Generate U a
| add {a b: α} : Generate U a -> Generate U b -> Generate U (a + b)
| mul {a b: α} : Generate U a -> Generate U b -> Generate U (a * b)
| neg {a: α} : Generate U a -> Generate U (-a)
| zero : Generate U 0
| one : Generate U 1

def generate (U: Set α) : Subring α where
  carrier := Set.mk (Generate U)
  mem_add := Generate.add
  mem_mul := Generate.mul
  mem_neg := Generate.neg
  mem_zero := Generate.zero
  mem_one := Generate.one

def copy (s: Subring α) (U: Set α) (h: s = U) : Subring α := {
  s.toAddSubgroupWithOne.copy U h, s.toSubsemigroup.copy U h with
}

end Subring
