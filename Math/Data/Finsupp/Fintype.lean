import Math.Data.Finsupp.Algebra
import Math.Data.Fintype.Algebra.Semiring
import Math.Data.Fintype.Impls.Finset

def sum_elem [Zero α] [Add α] [IsAddSemigroup α] [IsAddCommMagma α]
  (s: Finset ι) (f: ι -> α) : ∑i: s, f i.val = (s.val.map f).sum := by
  classical
  induction s using Finset.induction with
  | nil => simp; rfl
  | cons a as h ih =>
    rw [sum_eqv (Equiv.finset_insert_unique _ _ _).symm]
    simp
    simp [Finset.insert_unique]
    congr

namespace Finsupp

variable [FiniteSupport S ι]

def sum_eq_fintypesum
  [Zero α] [∀a: α, Decidable (a = 0)] [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ] (f: Finsupp ι α S) (g: ι -> α -> γ) (resp: ∀i: ι, f i = 0 -> g i (f i) = 0):
  f.sum g resp = ∑i: f.support, g i.val (f i.val) := by
  rw [sum_elem f.support (fun i => g i (f i))]
  rw [Finsupp.sum_eq_support_sum]

end Finsupp
