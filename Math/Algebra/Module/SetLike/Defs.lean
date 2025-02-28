import Math.Algebra.Monoid.Action.SetLike.Defs

class IsSubmodule (S R: Type*) {M: Type*} [SetLike S M] [Zero M] [Add M] [SMul R M] : Prop extends IsAddSubmonoid S,  IsSMulMem S R where

structure Submodule (R M: Type*) [Zero M] [Add M] [SMul R M] extends AddSubmonoid M,  SubMulAction M R where

namespace Submodule

variable [Zero M] [Add M] [SMul R M]

instance : SetLike (Submodule R M) M where
  coe s := s.carrier
  coe_inj := by
    intro a b eq; cases a; congr
    apply SetLike.coe_inj
    assumption

instance : IsSubmodule (Submodule R M) R where
  mem_zero s := s.mem_zero'
  mem_add s := s.mem_add'
  mem_smul s := s.mem_smul'

inductive Generate (U: Set M) : M -> Prop where
| of (x: M) : x ∈ U -> Generate U x
| zero : Generate U 0
| add : Generate U a -> Generate U b -> Generate U (a + b)
| smul (r: R) {a: M} : Generate U a -> Generate U (r • a)

def generate (U: Set M) : Submodule R M where
  carrier := Set.mk (Generate U)
  mem_zero' := Generate.zero
  mem_add' := Generate.add
  mem_smul' := Generate.smul

def of_mem_generate [SetLike S M] [IsSubmodule S R] (U: Set M) (s: S) :
  (∀x ∈ U, x ∈ s) -> (generate (R := R) U).carrier ⊆ s := by
  intro h x hx
  show x ∈ s
  induction hx with
  | of =>
    apply h
    assumption
  | zero => apply mem_zero
  | add => apply mem_add <;> assumption
  | smul => apply mem_smul <;> assumption

end Submodule
