import Math.Data.Poly.Defs
import Math.Algebra.Algebra.Hom

namespace Poly

section Eval

variable
  [SemiringOps P] [IsSemiring P]
  [SemiringOps M] [IsSemiring M]
  [SMul P M] [AlgebraMap P M] [IsAlgebra P M]

def eval (x: M) (p: P[X]) : M :=
  p.toFinsupp.sum (fun i p => p • x ^ i) (by
    intro i eq
    dsimp
    rw [eq, zero_smul])

def eval_C (x: M) (p: P) : eval x (C p) = algebraMap p := by
  unfold eval C
  erw [Finsupp.single_sum]
  rw [npow_zero, smul_one]

def eval_monomial (x: M) (n: ℕ) : eval x (monomial n: P[X]) = x ^ n := by
  unfold  eval
  erw [Finsupp.single_sum]
  rw [one_smul]

def eval_X (x: M) : eval x (X: P[X]) = x := by
  unfold X
  rw [eval_monomial, npow_one]

def eval_zero (x: M) : eval x (0: P[X]) = 0 := rfl
def eval_one (x: M) : eval x (1: P[X]) = 1 := by
  rw [←map_one (algebraMap (R := P)), ←C_eq_algebraMap', eval_C,
    map_one]
def eval_add (x: M) (a b: P[X]) : eval x (a + b) = eval x a + eval x b := by
  unfold eval
  apply Finsupp.add_sum
  intro i a b
  rw [add_smul]

private def eval_mul_X (x: M) (a: P[X]) : eval x (a * X) = eval x a * x := by
  rw [←X_mul_eq_mul_X]
  unfold eval X
  erw [AddMonoidAlgebra.mul_def, AddMonoidAlgebra.mul',
    Finsupp.single_sum]
  simp
  let f : M →+ M := {
    toFun y := y * x
    map_zero := by simp
    map_add := by simp [add_mul]
  }
  show _ = f _
  rw [Finsupp.map_sum]
  conv => {
    lhs; arg 1; rw [AddMonoidAlgebra.sum_toFinsupp (h₁ := by
      intro y h
      simp
      rw [h]
      ext
      rw [Finsupp.apply_single]
      split <;> rfl)]
  }
  simp
  rw [Finsupp.sum_sum_index]
  · congr
    ext n p
    rw [Finsupp.single_sum]
    show _ = _ * x
    rw [smul_def, smul_def, mul_assoc, ←npow_succ, add_comm]
  · intro i a b
    rw [add_smul]
  · intro
    ext
    rw [Finsupp.apply_single]
    split <;> rfl
  · intro; simp

instance (x: M) (a: P[X]) : IsCommutes x (eval x a) where
  mul_commutes := by
    induction a with
    | C a => rw [eval_C, commutes]
    | monomial p n ih => rw [npow_succ, ←mul_assoc, eval_mul_X, ←mul_assoc, ih]
    | add a b iha ihb => rw [eval_add, add_mul, mul_add, iha, ihb]

instance (x: M) (a: P[X]) : IsCommutes (eval x a) x :=
  inferInstance

def eval_mul (x: M) (a b: P[X]) : eval x (a * b) = eval x a * eval x b := by
  induction a generalizing b with
  | C a =>
    rw [eval_C]
    induction b with
    | C b => simp [←map_mul, eval_C]
    | monomial b n ih =>
      rw [npow_succ, ←mul_assoc, ←mul_assoc, eval_mul_X, mul_assoc, ih,
         ←mul_assoc, eval_mul_X, mul_assoc]
    | add b₀ b₁ ih₀ ih₁ =>
      rw [eval_add, mul_add, eval_add, ih₀, ih₁, mul_add]
  | add b₀ b₁ ih₀ ih₁ =>
    rw [add_mul, eval_add, eval_add, add_mul, ih₀, ih₁]
  | monomial a n ih =>
    rw [npow_succ, mul_assoc, mul_assoc, X_mul_eq_mul_X,
      ←mul_assoc, ←mul_assoc, eval_mul_X, ih, ←mul_assoc, eval_mul_X,
        mul_assoc, mul_assoc, mul_comm x]

def evalHom (x: M) : P[X] →ₐ[P] M where
  toFun := eval x
  map_add := eval_add x _ _
  map_mul := eval_mul x _ _
  map_algebraMap := eval_C x

def evalHom_C (x: M) (p: P) : evalHom x (C p) = algebraMap p := eval_C _ _
def evalHom_X (x: M) : evalHom x (X: P[X]) = x := eval_X _

end Eval

section EvalWith

variable [SemiringOps P] [SemiringOps M] [FunLike F P M]
  [IsZeroHom F P M] [IsOneHom F P M] [IsAddHom F P M] [IsMulHom F P M]
  [IsSemiring P] [IsSemiring M] [IsCommMagma M]
  (f: F)

set_option linter.unusedVariables false in
private def ofHom (P M: Type*) (f: F) := M

namespace ofHom

private def get : ofHom P M f -> M := id

instance : SemiringOps (ofHom P M f) := inferInstanceAs (SemiringOps M)
instance : IsSemiring (ofHom P M f) := inferInstanceAs (IsSemiring M)

instance : AlgebraMap P (ofHom P M f) :=
  AlgebraMap.ofHom (toRingHom f)

instance : SMul P (ofHom P M f) where
  smul p m := f p * m.get

instance : IsAlgebra P (ofHom P M f) where
  commutes _ _ := mul_comm (α := M) _ _
  smul_def _ _ := rfl

end ofHom

def evalWith (x: M) (p: P[X]) : M :=
  eval (M := ofHom P M f) x p

def evalWith_C (x: M) (p: P) : evalWith f x (C p) = f p :=
  eval_C (M := ofHom P M f) _ _
def evalWith_X (x: M) : evalWith f x X = x :=
  eval_X (M := ofHom P M f) _
def evalWith_zero (x: M) : evalWith f x 0 = 0 :=
  eval_zero (M := ofHom P M f) _
def evalWith_one (x: M) : evalWith f x 1 = 1 :=
  eval_one (M := ofHom P M f) _

def evalWith_add (x: M) (a b: P[X]) : evalWith f x (a + b) = evalWith f x a + evalWith f x b :=
  eval_add (M := ofHom P M f) _ _ _
def evalWith_mul (x: M) (a b: P[X]) : evalWith f x (a * b) = evalWith f x a * evalWith f x b :=
  eval_mul (M := ofHom P M f) _ _ _

def evalWithHom (x: M) : P[X] →+* M where
  toFun := evalWith f x
  map_zero := evalWith_zero _ _
  map_one := evalWith_one _ _
  map_add := evalWith_add _ _ _ _
  map_mul := evalWith_mul _ _ _ _

def evalWithHom_C (x: M) (p: P) : evalWithHom f x (C p) = f p := evalWith_C _ _ _
def evalWithHom_X (x: M) : evalWithHom f x (X: P[X]) = x := evalWith_X _ _

end EvalWith

section Lift

variable
  [SemiringOps P] [SemiringOps A] [FunLike F P A]
  [IsSemiring P] [IsSemiring A]
  [SMul P A] [AlgebraMap P A] [IsAlgebra P A]

-- show that P[X] is the free commutative P-algebra over a single variable
def lift : A ≃ (P[X] →ₐ[P] A) where
  toFun := evalHom
  invFun f := f X
  leftInv x := by simp [evalHom_X]
  rightInv f := by
    ext p; dsimp
    induction p using alg_induction with
    | C p => rw [evalHom_C, C_eq_algebraMap', map_algebraMap]
    | X => simp [evalHom_X]
    | add a b iha ihb => simp [iha, ihb, map_add]
    | mul a b iha ihb => simp [iha, ihb, map_mul]

def apply_lift_C (x: A) (p: P) : lift x (C p) = algebraMap p := eval_C _ _
def apply_lift_X (x: A) : lift x (X: P[X]) = x := eval_X _

def lift_X (p: P[X]) [IsCommMagma P] : lift (X: P[X]) p = p := by
  induction p using alg_induction with
  | C a => rw [apply_lift_C]; rfl
  | X => rw [apply_lift_X]
  | add a b iha ihb => rw [map_add, iha, ihb]
  | mul a b iha ihb => rw [map_mul, iha, ihb]

end Lift

section Cast

variable {R: Type*} (P: Type*) [SemiringOps P] [SemiringOps R] [SemiringOps S]
   [IsSemiring P] [IsSemiring R] [IsSemiring S]
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

@[simp] def cast_self [IsCommMagma P] : cast P (R := P) = .id _ := by
  apply DFunLike.ext; intro x
  induction x using alg_induction with
  | C | X => simp; try rfl
  | add _ _ iha ihb | mul _ _ iha ihb => simp [iha, ihb]

instance : IsAlgebraTower S R P[X] where
  algebraMap_algebraMap s := by rw [←C_eq_algebraMap, algebraMap_algebraMap]; rfl

instance (priority := 200) : AlgebraMap R[X] P[X] := AlgebraMap.ofHom (cast P).toRingHom
instance : SMul R[X] P[X] where
  smul r x := algebraMap r * x
instance [IsCommMagma P] : IsAlgebra R[X] P[X] where
  commutes r p := by rw [mul_comm]
  smul_def _ _ := rfl

instance : IsAlgebraTower S R[X] P[X] where
  algebraMap_algebraMap s := by
    show cast P (algebraMap s: R[X]) = _
    simp

instance : IsAlgebraTower S[X] R[X] P[X] where
  algebraMap_algebraMap s := by
    show cast P (cast R s) = cast P s
    simp

end Cast

end Poly
