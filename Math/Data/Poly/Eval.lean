import Math.Data.Poly.Defs
import Math.Algebra.Basic

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
    rw [eq, resp_zero, zero_mul])

def evalWith_C (x: M) (p: P) : evalWith f x (C p) = f p := by
  unfold evalWith
  show Finsupp.sum (Finsupp.single _ _) _ _ = _
  rw [Finsupp.single_sum, npow_zero, mul_one]

def evalWith_zero (x: M) : evalWith f x (0: P[X]) = 0 := rfl
def evalWith_one (x: M) : evalWith f x (1: P[X]) = 1 := by
  show evalWith f x (C 1) = 1
  rw [evalWith_C, resp_one]

def evalWith_monomial (x: M) (n: ℕ) : evalWith f x (monomial n: P[X]) = x ^ n := by
  unfold evalWith
  show Finsupp.sum (Finsupp.single _ _) _ _ = _
  rw [Finsupp.single_sum, resp_one, one_mul]
def evalWith_X (x: M) : evalWith f x (X: P[X]) = x := by
  unfold X
  rw [evalWith_monomial, npow_one]

def evalWith_add (x: M) (a b: P[X]) : evalWith f x (a + b) = evalWith f x a + evalWith f x b := by
  unfold evalWith
  apply Finsupp.add_sum
  intro i a b
  rw [resp_add, add_mul]

def evalWith_mul_X (x: M) (p: P[X]) : evalWith f x (p * X) = evalWith f x p * x := by
  rw [←evalWith_X f x (P := P)]
  rw [evalWith]
  rw (occs := [3]) [evalWith]
  rw [evalWith_X]
  let f' : M →+ M := {
    toFun := (· * x)
    resp_zero := zero_mul _
    resp_add := add_mul _ _ _
  }
  show _ = f' _
  rw [Finsupp.resp_sum]
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
  rw [resp_add, add_mul]
  intro i
  simp; rfl
  intro i
  simp [resp_zero]

def evalWith_mul (x: M) (a b: P[X]) : evalWith f x (a * b) = evalWith f x a * evalWith f x b := by
  induction a generalizing b with
  | C =>
    induction b with
    | C =>
      rw [←resp_mul, evalWith_C, evalWith_C, evalWith_C]
      rw [resp_mul]
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
  resp_zero := evalWith_zero _ _
  resp_one := evalWith_one _ _
  resp_add := evalWith_add _ _ _ _
  resp_mul := evalWith_mul _ _ _ _

def evalWithHom_C (x: M) (p: P) : evalWithHom f x (C p) = f p := evalWith_C _ _ _
def evalWithHom_X (x: M) : evalWithHom f x (X: P[X]) = x := evalWith_X _ _

end EvalWith

section Semiring

variable [SemiringOps P] [IsSemiring P]
   [SemiringOps M] [IsSemiring M] [IsAddCommMagma M] [IsCommMagma M]
  [SMul P M] [AlgebraMap P M] [IsAlgebra P M] [IsCommMagma P]

def eval (x: M) (p: P[X]) : M :=
  p.evalWith (F := P →+* M) algebraMap x

def evalHom (x: M) : P[X] →+* M := evalWithHom algebraMap x

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

end Poly
