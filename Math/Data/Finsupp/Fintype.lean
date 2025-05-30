import Math.Data.Finsupp.Algebra
import Math.Data.Fintype.Algebra.Semiring
import Math.Data.Fintype.Impls.LazyFinset

variable [DecidableEq ι]

def sum_elem [Zero α] [Add α] [IsAddSemigroup α] [IsAddCommMagma α]
  (s: LazyFinset ι) (f: ι -> α) : ∑i: s, f i.val = (s.toMultiset.map f).sum := by
  classical
  induction s with
  | nil => simp
  | cons a as h ih =>
    rw [sum_eqv (Equiv.lazy_finset_cons_unique _ _ h).symm]
    rw [LazyFinset.cons_toMultiset _ _ h]
    simp
    congr

namespace Finsupp

variable [FiniteSupport S ι]

def sum_eq_fintypesum
  [Zero α] [∀a: α, Decidable (a = 0)] [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ] (f: Finsupp ι α S) (g: ι -> α -> γ) (resp: ∀i: ι, f i = 0 -> g i (f i) = 0):
  f.sum g resp = ∑i: f.support, g i.val (f i.val) := by
  rw [sum_elem f.support (fun i => g i (f i))]
  rw [Finsupp.sum_eq_support_sum]

end Finsupp
