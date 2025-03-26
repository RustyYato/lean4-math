import Math.Algebra.Impls.Pi
import Math.Algebra.QuadraticForm.Basic
import Math.Data.Fintype.Algebra

@[local simp]
private def pi_add [Add R] : ∀{ι} (a b: ι -> R) (x: ι), (a + b) x = a x + b x :=
   fun _ _ _ => rfl

namespace QuadraticForm

-- a non-negative signature where the basis vectors from [p, p+n) all square to 1
private def ofNonnegSignature' [SemiringOps R] [IsSemiring R] [IsCommMagma R] (z p n: ℕ) : QuadraticForm R (Fin (z + p + n) -> R) where
  toFun v :=
    ∑x: Fin p,
      let x := (x.natAdd z).castAdd n
      v x * v x
  toFun_smul a v := by
    dsimp
    rw [smul_eq_mul, mul_sum]
    congr; ext i
    simp [SMul.smul]
    ac_rfl
  exists_companion' := by
    refine ⟨?_, ?_⟩
    apply BilinMap.mk (fun a b =>
      ∑x: Fin p, 2 * a ((x.natAdd z).castAdd n) * b ((x.natAdd z).castAdd n))
    · intro a b k
      rw [sum_add_sum]
      congr; ext i
      rw [←add_mul, ←mul_add]
      rfl
    · intro k a b
      rw [sum_add_sum]
      congr; ext i
      rw [←mul_add]
      rfl
    · intro r a k
      simp [mul_sum]
      congr; ext i
      rw [←mul_assoc, mul_left_comm]
      ac_rfl
    · intro r a k
      simp [mul_sum]
      congr; ext i
      rw [mul_left_comm]
    · intro a b
      simp [DFunLike.coe, BilinMap.mk]
      rw [sum_add_sum, sum_add_sum]
      congr; ext i
      simp [add_mul, mul_add, two_mul]
      ac_nf

-- a non-negative signature where the basis vectors from p<= all square to 1
def ofNonnegSignature [SemiringOps R] [IsSemiring R] [IsCommMagma R] (z p: ℕ) : QuadraticForm R (Fin (z + p) -> R)
 := ofNonnegSignature' z p 0

-- a signature where the basis vectors from [p, p+n) all square to 1 and p+n <=  square to -1
def ofSignature [RingOps R] [IsRing R] [IsCommMagma R] (z p n: ℕ) : QuadraticForm R (Fin (z + p + n) -> R) :=
  have a: QuadraticForm R (Fin (z + p + n) → R) := QuadraticForm.ofNonnegSignature' (R := R) z p n
  have b: QuadraticForm R (Fin (z + p + n) → R) := QuadraticForm.ofNonnegSignature' (R := R) (z + p) n 0
  a - b

def ofSignature' [RingOps R] [IsRing R] [IsCommMagma R] (z p n: ℕ) (k: ℕ) (keq: k = z + p + n) : QuadraticForm R (Fin k -> R) where
  toFun v := QuadraticForm.ofSignature z p n (fun x => v (x.cast keq.symm))
  toFun_smul a v := by
    dsimp
    apply QuadraticMap.toFun_smul
  exists_companion' := by
    subst k
    apply QuadraticMap.exists_companion

end QuadraticForm
