import Math.Algebra.Semiring.Hom

instance [SemiringOps R] [IsSemiring R] : Subsingleton (AlgebraMap ℕ R) where
  allEq := by
    intro a b
    cases a with | mk a =>
    cases b with | mk b =>
    congr; apply Subsingleton.allEq
