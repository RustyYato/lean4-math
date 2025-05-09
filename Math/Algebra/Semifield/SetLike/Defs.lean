import Math.Algebra.Semiring.SetLike.Defs
import Math.Algebra.GroupWithZero.SetLike.Defs

variable (S: Type*) {α: Type*} [SetLike S α]

class IsSubsemifield [Zero α] [One α] [CheckedInv? α] [Add α] [Mul α]
  : Prop extends IsSubsemiring S, IsSubgroupWithZero S where

structure Subsemifield (α: Type*) [Zero α] [One α] [CheckedInv? α] [Add α] [Mul α]
  extends Subsemiring α, SubgroupWithZero α where

namespace Subsemifield

variable [Zero α] [One α] [CheckedInv? α] [Add α] [Mul α]

instance : SetLike (Subsemifield α) α where
  coe s := s.carrier
  coe_inj := by
    intro a b eq; cases a; congr
    apply SetLike.coe_inj; assumption

instance : IsSubsemifield (Subsemifield α) where
  mem_zero s := s.mem_zero
  mem_one s := s.mem_one
  mem_inv? s := s.mem_inv?
  mem_add s := s.mem_add
  mem_mul s := s.mem_mul

inductive Generate (U: Set α) : α -> Prop where
| of (a: α) : a ∈ U -> Generate U a
| mul {a b: α} : Generate U a -> Generate U b -> Generate U (a * b)
| add {a b: α} : Generate U a -> Generate U b -> Generate U (a + b)
| inv? {a: α} (h: a ≠ 0) : Generate U a -> Generate U (a⁻¹?)
| one : Generate U 1
| zero : Generate U 0

def generate (U: Set α) : Subsemifield α where
  carrier := Set.mk (Generate U)
  mem_mul := Generate.mul
  mem_add := Generate.add
  mem_inv? := Generate.inv?
  mem_one := Generate.one
  mem_zero := Generate.zero

end Subsemifield
