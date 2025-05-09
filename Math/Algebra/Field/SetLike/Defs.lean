import Math.Algebra.Ring.SetLike.Defs
import Math.Algebra.Semifield.SetLike.Defs
import Math.Algebra.GroupWithZero.SetLike.Defs

variable (S: Type*) {α: Type*} [SetLike S α]

class IsSubfield [Zero α] [One α] [Neg α] [CheckedInv? α] [Add α] [Mul α]
  : Prop extends IsSubring S, IsSubsemifield S where

structure Subfield (α: Type*) [Zero α] [One α] [Neg α] [CheckedInv? α] [Add α] [Mul α]
  extends Subring α, Subsemifield α where

namespace Subfield

variable [Zero α] [One α] [Neg α] [CheckedInv? α] [Add α] [Mul α]

instance : SetLike (Subfield α) α where
  coe s := s.carrier
  coe_inj := by
    intro a b eq; cases a; congr
    apply SetLike.coe_inj; assumption

instance : IsSubfield (Subfield α) where
  mem_zero s := s.mem_zero
  mem_one s := s.mem_one
  mem_neg s := s.mem_neg
  mem_inv? s := s.mem_inv?
  mem_add s := s.mem_add
  mem_mul s := s.mem_mul

inductive Generate (U: Set α) : α -> Prop where
| of (a: α) : a ∈ U -> Generate U a
| mul {a b: α} : Generate U a -> Generate U b -> Generate U (a * b)
| add {a b: α} : Generate U a -> Generate U b -> Generate U (a + b)
| inv? {a: α} (h: a ≠ 0) : Generate U a -> Generate U (a⁻¹?)
| neg {a: α} : Generate U a -> Generate U (-a)
| one : Generate U 1
| zero : Generate U 0

def generate (U: Set α) : Subfield α where
  carrier := Set.mk (Generate U)
  mem_mul := Generate.mul
  mem_add := Generate.add
  mem_inv? := Generate.inv?
  mem_neg := Generate.neg
  mem_one := Generate.one
  mem_zero := Generate.zero

def of_mem_generate {S: Type*} [SetLike S α] [IsSubfield S] (U: Set α) (s: S) :
  (∀x ∈ U, x ∈ s) -> ∀x ∈ generate U, x ∈ s := by
  intro h x hx
  show x ∈ s
  induction hx with
  | of =>
    apply h
    assumption
  | zero => apply mem_zero <;> assumption
  | one => apply mem_one <;> assumption
  | neg => apply mem_neg <;> assumption
  | inv? => apply mem_inv? <;> assumption
  | add => apply mem_add <;> assumption
  | mul => apply mem_mul <;> assumption

def copy (s: Subfield α) (U: Set α) (h: s = U) : Subfield α := {
  s.toAddSubgroupWithOne.copy U h, s.toSubgroupWithZero.copy U h with
}

end Subfield
