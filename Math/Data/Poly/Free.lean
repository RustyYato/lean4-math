import Math.Data.Free.Algebra
import Math.Data.Poly.Eval
import Math.Algebra.RingQuot

-- show that polynomials are precicely the free algebra over a
-- commutative semiring

open Poly

variable {P X} [SemiringOps P] [IsSemiring P] [IsCommMagma P]

-- Polynomials are algebraically equivalent to the commutative free algebra
def poly_equiv_free_alg : P[X] ≃ₐ[P] FreeAlgebra P Unit := AlgEquiv.symm {
  FreeAlgebra.lift P (fun x => Poly.X) with
  invFun := evalHom (FreeAlgebra.ι P ())
  rightInv := by
    intro p
    simp
    induction p using Poly.alg_induction with
    | C => rw [evalHom_C, map_algebraMap]; rfl
    | X => rw [evalHom_X, FreeAlgebra.lift_ι_apply]
    | add => rw [map_add, map_add]; congr
    | mul => rw [map_mul, map_mul]; congr
  leftInv := by
    intro p
    simp
    induction p with
    | grade0 r => rw [map_algebraMap, map_algebraMap]
    | grade1 => rw [FreeAlgebra.lift_ι_apply, evalHom_X]
    | add _ _ => rw [map_add, map_add]; congr
    | mul => rw [map_mul, map_mul]; congr
}
