import Math.Algebra.Algebra.Defs
import Math.Algebra.Hom.Defs
import Math.Algebra.AddGroupWithOne.Hom
import Math.Algebra.Ring.Basic

section

variable (A B C: Type*) [SemiringOps A] [IsSemiring A] [SemiringOps B] [IsSemiring B]
   [SemiringOps C] [IsSemiring C]
   [AlgebraMap A B] [AlgebraMap B C] [AlgebraMap A C]
   [SMul A B] [SMul B C] [SMul A C]
   [IsAlgebra A B] [IsAlgebra B C] [IsAlgebra A C]

instance : IsAlgebraTower ℕ A B where
  algebraMap_algebraMap n := by
    show algebraMap (algebraMap (Nat.cast n: ℕ)) = algebraMap (Nat.cast n: ℕ)
    simp only [map_natCast]

end

section

variable (A B C: Type*) [RingOps A] [IsRing A] [RingOps B] [IsRing B]
   [RingOps C] [IsRing C]
   [AlgebraMap A B] [AlgebraMap B C] [AlgebraMap A C]
   [SMul A B] [SMul B C] [SMul A C]
   [IsAlgebra A B] [IsAlgebra B C] [IsAlgebra A C]

instance : IsAlgebraTower ℤ A B where
  algebraMap_algebraMap n := by
    show algebraMap (algebraMap (Int.cast n: ℤ)) = algebraMap (Int.cast n: ℤ)
    simp only [map_intCast]

end
