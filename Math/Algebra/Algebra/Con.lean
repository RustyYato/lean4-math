import Math.Algebra.Semiring.Con
import Math.Algebra.Algebra.Defs

variable {C R: Type*} [RelLike C R]
  [SemiringOps R] [SemiringOps S]
  [IsSemiring R] [IsSemiring S] [IsRingCon C]
  [SMul S R] [AlgebraMap S R] [IsAlgebra S R]
  (c: C)

instance : IsSMulCon C S where
  resp_smul c s {a b} h := by
    rw [smul_def, smul_def]
    apply resp_mul
    rfl
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
