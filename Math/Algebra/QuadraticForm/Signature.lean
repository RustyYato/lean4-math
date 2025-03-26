import Math.Algebra.Impls.Pi
import Math.Algebra.QuadraticForm.Basic
import Math.Data.Fintype.Algebra

@[local simp]
private def pi_add [Add R] : ∀{ι} (a b: ι -> R) (x: ι), (a + b) x = a x + b x :=
   fun _ _ _ => rfl

namespace QuadraticForm

section

variable [SemiringOps R] [IsSemiring R] [IsCommMagma R]

def single (i: ι) : QuadraticForm R (ι -> R) where
  toFun f := f i * f i
  toFun_smul := by
    intro a x
    simp
    ac_rfl
  exists_companion' := by
    simp
    refine ⟨?_, ?_⟩
    · apply BilinMap.mk
      case f =>
        intro f g
        exact 2 * f i * g i
      case resp_add_left =>
        intro a b k
        simp [mul_add, add_mul]
      case resp_add_right =>
        intro k a b
        simp [mul_add, add_mul]
      case resp_smul_left =>
        intro r' a k
        simp; ac_rfl
      case resp_smul_right =>
        intro r' a k
        simp; ac_rfl
    · intro x y
      simp [mul_assoc, ←npow_two, square_add, two_mul]
      simp [npow_two, mul_add, add_mul]
      ac_rfl

-- a non-negative signature where the basis vectors {v | p <= v} all square to 1
def ofNonnegSignature (z p: ℕ) : QuadraticForm R (Fin (z + p) -> R) :=
  ∑i: Fin p, single (i.natAdd z)

end

section

variable [RingOps R] [IsRing R] [IsCommMagma R]

-- a signature where the basis vectors {v | p <= v < p + n} all square to 1
-- and the basis vectors {v | p + n <= v} all square to -1
def ofSignature (z p n: ℕ) : QuadraticForm R (Fin (z + p + n) -> R) :=
  (∑i: Fin p, single ((i.natAdd z).castAdd n)) -
  (∑i: Fin n, single (i.natAdd (z + p)))

-- a signature where the basis vectors {v | p <= v < p + n} all square to 1
-- and the basis vectors {v | p + n <= v} all square to -1
def ofSignature' (z p n k: ℕ) (h: k = z + p + n) : QuadraticForm R (Fin k -> R) where
  toFun f := ofSignature z p n (f ∘ Fin.cast h.symm)
  toFun_smul := by
    subst h
    apply (ofSignature z p n).toFun_smul
  exists_companion' := by
    subst h
    apply (ofSignature z p n).exists_companion'

end

end QuadraticForm
