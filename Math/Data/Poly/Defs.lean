import Math.Algebra.Monoid.MonoidAlgebra

def Poly (α: Type*) [Zero α] := AddMonoidAlgebra ℕ α ℕ

namespace Poly

instance [SemiringOps α] [IsSemiring α] : Add (Poly α) :=
  inferInstanceAs (Add (AddMonoidAlgebra _ _ _))
instance [SemiringOps α] [IsSemiring α] : SMul ℕ (Poly α) :=
  inferInstanceAs (SMul ℕ (AddMonoidAlgebra _ _ _))
instance [SemiringOps α] [IsSemiring α] : Zero (Poly α) :=
  inferInstanceAs (Zero (AddMonoidAlgebra _ _ _))
instance [SemiringOps α] [IsSemiring α] : IsAddMonoid (Poly α) :=
  inferInstanceAs (IsAddMonoid (AddMonoidAlgebra _ _ _))

instance [RingOps α] [IsRing α] : Sub (Poly α) :=
  inferInstanceAs (Sub (AddMonoidAlgebra _ _ _))
instance [RingOps α] [IsRing α] : Neg (Poly α) :=
  inferInstanceAs (Neg (AddMonoidAlgebra _ _ _))
instance [RingOps α] [IsRing α] : SMul ℤ (Poly α) :=
  inferInstanceAs (SMul ℤ (AddMonoidAlgebra _ _ _))
instance [RingOps α] [IsRing α] : IsAddGroup (Poly α) :=
  inferInstanceAs (IsAddGroup (AddMonoidAlgebra _ _ _))

instance [SemiringOps α] [IsSemiring α] : Mul (Poly α) :=
  inferInstanceAs (Mul (AddMonoidAlgebra _ _ _))

end Poly
