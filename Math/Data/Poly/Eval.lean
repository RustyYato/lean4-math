import Math.Data.Poly.Defs
import Math.Algebra.Algebra.Hom

namespace Poly

section EvalWith

variable [SemiringOps P] [SemiringOps M] [FunLike F P M]
  [IsZeroHom F P M] [IsOneHom F P M] [IsAddHom F P M] [IsMulHom F P M]
  [IsSemiring P] [IsSemiring M] [IsCommMagma P] [IsCommMagma M]
  (f: F)

def evalWith (x: M) (p: P[X]) : M :=
  p.toFinsupp.sum (fun i p => f p * x ^ i) (by
    intro i eq
    dsimp
    rw [eq, map_zero, zero_mul])

def evalWith_C (x: M) (p: P) : evalWith f x (C p) = f p := by
  unfold evalWith
  show Finsupp.sum (Finsupp.single _ _) _ _ = _
  rw [Finsupp.single_sum, npow_zero, mul_one]

def evalWith_zero (x: M) : evalWith f x (0: P[X]) = 0 := rfl
def evalWith_one (x: M) : evalWith f x (1: P[X]) = 1 := by
  show evalWith f x (C 1) = 1
  rw [evalWith_C, map_one]

def evalWith_monomial (x: M) (n: ℕ) : evalWith f x (monomial n: P[X]) = x ^ n := by
  unfold evalWith
  show Finsupp.sum (Finsupp.single _ _) _ _ = _
  rw [Finsupp.single_sum, map_one, one_mul]
def evalWith_X (x: M) : evalWith f x (X: P[X]) = x := by
  unfold X
  rw [evalWith_monomial, npow_one]

def evalWith_add (x: M) (a b: P[X]) : evalWith f x (a + b) = evalWith f x a + evalWith f x b := by
  unfold evalWith
  apply Finsupp.add_sum
  intro i a b
  rw [map_add, add_mul]

def evalWith_mul_X (x: M) (p: P[X]) : evalWith f x (p * X) = evalWith f x p * x := by
  rw [←evalWith_X f x (P := P)]
  rw [evalWith]
  rw (occs := [3]) [evalWith]
  rw [evalWith_X]
  let f' : M →+ M := {
    toFun := (· * x)
    map_zero := zero_mul _
    map_add := add_mul _ _ _
  }
  show _ = f' _
  rw [Finsupp.map_sum]
  unfold f'
  simp [DFunLike.coe, mul_assoc, ←npow_succ]
  rw [←X_mul_eq_mul_X, AddMonoidAlgebra.mul_def]
  unfold AddMonoidAlgebra.mul' X monomial
  erw [Finsupp.single_sum]
  simp
  conv => {
    lhs; arg 1; rw [AddMonoidAlgebra.sum_toFinsupp (h₁ := by
      intro i eq
      rw [eq]
      simp; rfl)]
  }
  rw [Finsupp.sum_sum_index]
  conv => { lhs; arg 2; intro a b; erw [Finsupp.single_sum] }
  congr; ext a b
  rw [add_comm]
  intro i a b
  rw [map_add, add_mul]
  intro i
  simp; rfl
  intro i
  simp [map_zero]

def evalWith_mul (x: M) (a b: P[X]) : evalWith f x (a * b) = evalWith f x a * evalWith f x b := by
  induction a generalizing b with
  | C =>
    induction b with
    | C =>
      rw [←map_mul, evalWith_C, evalWith_C, evalWith_C]
      rw [map_mul]
    | monomial =>
      rename_i a r n ih
      rw [npow_succ, ←mul_assoc (C r),  evalWith_mul_X, ←mul_assoc (evalWith f x _),
        ←ih, ←evalWith_mul_X]
      ac_rfl
    | add =>
      rename_i p a b iha ihb
      rw [mul_add, evalWith_add, iha, ihb, ←mul_add, ←evalWith_add]
  | monomial _ _ ih =>
    rw [npow_succ, ←mul_assoc (C _),
      evalWith_mul_X, mul_comm_right _ x,
      ←ih, ←evalWith_mul_X, mul_comm_right]
  | add _ _ ih₀ ih₁ =>
    rw [add_mul, evalWith_add, ih₀, ih₁, evalWith_add, add_mul]

def evalWithHom (x: M) : P[X] →+* M where
  toFun := evalWith f x
  map_zero := evalWith_zero _ _
  map_one := evalWith_one _ _
  map_add := evalWith_add _ _ _ _
  map_mul := evalWith_mul _ _ _ _

def evalWithHom_C (x: M) (p: P) : evalWithHom f x (C p) = f p := evalWith_C _ _ _
def evalWithHom_X (x: M) : evalWithHom f x (X: P[X]) = x := evalWith_X _ _

end EvalWith

section Semiring

variable [SemiringOps P] [IsSemiring P]
   [SemiringOps M] [IsSemiring M] [IsAddCommMagma M] [IsCommMagma M]
  [SMul P M] [AlgebraMap P M] [IsAlgebra P M] [IsCommMagma P]

def eval (x: M) (p: P[X]) : M :=
  p.evalWith algebraMap x

def evalHom (x: M) : P[X] →ₐ[P] M := {
  evalWithHom algebraMap x with
  map_algebraMap := evalWith_C _ _
}

def evalHom_C (x: M) (p: P) : evalHom x (C p) = algebraMap p := evalWith_C _ _ _
def evalHom_X (x: M) : evalHom x (X: P[X]) = x := evalWith_X _ _

def eval_C (x: M) (p: P) : eval x (C p) = algebraMap p := evalWith_C _ _ _
def eval_X (x: M) : eval x (X: P[X]) = x := evalWith_X _ _
def eval_zero (x: M) : eval x (0: P[X]) = 0 := rfl
def eval_one (x: M) : eval x (1: P[X]) = 1 := evalWith_one _ _
def eval_monomial (x: M) (n: ℕ) : eval x (monomial n: P[X]) = x ^ n :=
  evalWith_monomial _ _ _
def eval_add (x: M) (a b: P[X]) : eval x (a + b) = eval x a + eval x b :=
  evalWith_add _ _ _ _
def eval_mul (x: M) (a b: P[X]) : eval x (a * b) = eval x a * eval x b :=
  evalWith_mul _ _ _ _

end Semiring

section Lift

variable [SemiringOps P] [SemiringOps A] [FunLike F P A]
  [IsSemiring P] [IsSemiring A] [IsCommMagma P] [IsCommMagma A]
  [DecidableEq σ] [SMul P A] [AlgebraMap P A] [IsAlgebra P A]

-- show that P[X] is the free commutative P-algebra over a single variable
def lift : A ≃ (P[X] →ₐ[P] A) where
  toFun := evalHom
  invFun x := x X
  leftInv f := by simp [evalHom_X]
  rightInv f := by
    ext p
    simp
    induction p using alg_induction with
    | C p =>
      show _ = f (algebraMap p)
      rw [evalHom_C, map_algebraMap]
    | X => simp [evalHom_X]
    | add a b iha ihb => simp [iha, ihb, map_add]
    | mul a b iha ihb => simp [iha, ihb, map_mul]

def apply_lift_C (x: A) (p: P) : lift x (C p) = algebraMap p := evalWith_C _ _ _
def apply_lift_X (x: A) : lift x (X: P[X]) = x := evalWith_X _ _

def lift_X : lift (X: P[X]) x = x := by
  induction x using alg_induction with
  | C a => rw [apply_lift_C]; rfl
  | X => rw [apply_lift_X]
  | add a b iha ihb => rw [map_add, iha, ihb]
  | mul a b iha ihb => rw [map_mul, iha, ihb]

end Lift

section Cast

variable {R: Type*} (P: Type*) [SemiringOps P] [SemiringOps R] [SemiringOps S]
   [IsSemiring P] [IsSemiring R] [IsCommMagma P] [IsCommMagma R] [IsSemiring S] [IsCommMagma S]
  [SMul R P] [AlgebraMap R P] [IsAlgebra R P]
  [SMul S R] [AlgebraMap S R] [IsAlgebra S R]
  [SMul S P] [AlgebraMap S P] [IsAlgebra S P]
  [IsAlgebraTower S R P]

def cast : R[X] →ₐ[R] P[X] := lift Poly.X

@[simp] def apply_cast_C (r: R) : cast P (C r) = C (algebraMap r) := apply_lift_C _ _
@[simp] def apply_cast_X : cast P (.X: R[X]) = .X := apply_lift_X _
@[simp] def apply_cast_add (a b: R[X]) : cast P (a + b) = cast P a + cast P b := map_add _
@[simp] def apply_cast_mul (a b: R[X]) : cast P (a * b) = cast P a * cast P b := map_mul _
@[simp] def apply_cast_algebraMap (s: S) : cast P (algebraMap s: R[X]) = algebraMap s := by
  rw [←C_eq_algebraMap, apply_cast_C, algebraMap_algebraMap]; rfl
@[simp] def apply_cast_smul (s: S) (a: R[X]) : cast P (s • a) = s • cast P a := by simp [smul_def]

@[simp] def cast_cast (x: S[X]) : cast P (cast R x) = cast P x := by
  induction x using alg_induction with
  | X => simp
  | add _ _ iha ihb | mul _ _ iha ihb => simp [iha, ihb]
  | C =>
    simp
    rw [algebraMap_algebraMap]

@[simp] def cast_self : cast P (R := P) = .id _ := by
  apply DFunLike.ext; intro x
  induction x using alg_induction with
  | C | X => simp; try rfl
  | add _ _ iha ihb | mul _ _ iha ihb => simp [iha, ihb]

instance : IsAlgebraTower S R P[X] where
  algebraMap_algebraMap s := by rw [←C_eq_algebraMap, algebraMap_algebraMap]; rfl

end Cast

end Poly
