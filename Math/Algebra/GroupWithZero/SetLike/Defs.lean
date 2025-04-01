import Math.Algebra.Group.SetLike.Defs
import Math.Ops.Checked

variable (S: Type*) {α: Type*} [SetLike S α]

class IsInv?Mem [Zero α] [CheckedInv? α] : Prop where
  mem_inv? (s: S) {a: α} (nz: a ≠ 0) (h: a ∈ s) : a⁻¹? ∈ s

def mem_inv? {S α: Type*} [SetLike S α] [Zero α] [CheckedInv? α] [IsInv?Mem S] (s: S) {a: α} (nz: a ≠ 0) (h: a ∈ s) : a⁻¹? ∈ s := IsInv?Mem.mem_inv? s nz h

class IsSubgroupWithZero [Mul α] [One α] [Zero α] [CheckedInv? α] : Prop extends IsSubmonoid S, IsInv?Mem S, IsZeroMem S  where

structure SubgroupWithZero (α: Type*) [Mul α] [One α] [Zero α] [CheckedInv? α] extends Submonoid α where
  mem_inv?': ∀{a} (h: a ≠ 0), a ∈ carrier -> a⁻¹? ∈ carrier
  mem_zero: 0 ∈ carrier

namespace SubgroupWithZero

variable[Mul α] [One α] [Zero α] [CheckedInv? α]

instance : SetLike (SubgroupWithZero α) α where
  coe s := s.carrier
  coe_inj := by
    intro a b eq; cases a; congr
    apply SetLike.coe_inj; assumption

instance : IsSubgroupWithZero (SubgroupWithZero α) where
  mem_mul s := s.mem_mul
  mem_one s := s.mem_one
  mem_inv? s := s.mem_inv?'
  mem_zero s := s.mem_zero

inductive Generate (U: Set α) : α -> Prop where
| of (a: α) : a ∈ U -> Generate U a
| mul {a b: α} : Generate U a -> Generate U b -> Generate U (a * b)
| inv? {a: α} (h: a ≠ 0) : Generate U a -> Generate U (a⁻¹?)
| one : Generate U 1
| zero : Generate U 0

def generate (U: Set α) : SubgroupWithZero α where
  carrier := Set.mk (Generate U)
  mem_mul := Generate.mul
  mem_inv?' := Generate.inv?
  mem_one := Generate.one
  mem_zero := Generate.zero

end SubgroupWithZero
