import Math.Algebra.Semiring.Con
import Math.Algebra.Algebra.Defs

variable {C R: Type*} [RelLike C R]
  [SemiringOps R] [SemiringOps S]
  [IsSemiring R] [IsSemiring S] [IsRingCon C]
  [SMul S R] [AlgebraMap S R] [IsAlgebra S R]
  (c: C)

def resp_smul (c: C) (n: S) {a b: R} (h: c a b) : c (n • a) (n • b) := by
  rw [smul_def, smul_def]
  apply resp_mul
  rfl
  assumption

instance (priority := 900) : SMul S (IsCon.Quotient c) where
  smul s := by
    refine Quotient.lift ?_ ?_
    intro r
    exact IsCon.mkQuot c (s • r)
    intro a b h
    apply Quotient.sound
    apply resp_smul
    assumption

instance (priority := 900) : AlgebraMap S (IsCon.Quotient c) :=
  AlgebraMap.ofHom <| (IsRingCon.mkQuot c).comp algebraMap

instance (priority := 900) : IsAlgebra S (IsCon.Quotient c) where
  commutes s a := by
    induction a with | mk a =>
    apply Quotient.sound
    show c (algebraMap s * a) (a * algebraMap s)
    rw [commutes]
  smul_def s a := by
    induction a with | mk a =>
    apply Quotient.sound
    show c (s • a) (algebraMap s * a)
    rw [smul_def]
