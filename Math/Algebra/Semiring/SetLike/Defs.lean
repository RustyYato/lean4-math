import Math.Algebra.AddMonoidWithOne.SetLike.Defs

variable (S: Type*) {α: Type*} [SetLike S α]

class IsSubsemiring [Add α] [Mul α] [Zero α] [One α] : Prop extends IsAddSubmonoidWithOne S, IsSubmonoid S where

structure Subsemiring (α: Type*) [Add α] [Mul α] [Zero α] [One α] extends AddSubmonoidWithOne α, Submonoid α where

namespace Subsemiring

variable [Add α] [Mul α] [Zero α] [One α]

instance : SetLike (Subsemiring α) α where
  coe a := a.carrier
  coe_inj := by
    intro a b eq; cases a; congr
    apply SetLike.coe_inj
    assumption

instance : IsSubsemiring (Subsemiring α) where
  mem_add a := a.mem_add
  mem_mul a := a.mem_mul
  mem_zero a := a.mem_zero
  mem_one a := a.mem_one

@[ext]
def ext (a b: Subsemiring α) : (∀x, x ∈ a ↔ x ∈ b) -> a = b := SetLike.ext _ _

inductive Generate (U: Set α) : α -> Prop where
| of (a: α) : a ∈ U -> Generate U a
| add {a b: α} : Generate U a -> Generate U b -> Generate U (a + b)
| mul {a b: α} : Generate U a -> Generate U b -> Generate U (a * b)
| zero : Generate U 0
| one : Generate U 1

def generate (U: Set α) : Subsemiring α where
  carrier := Set.mk (Generate U)
  mem_add := Generate.add
  mem_mul := Generate.mul
  mem_zero := Generate.zero
  mem_one := Generate.one

end Subsemiring
