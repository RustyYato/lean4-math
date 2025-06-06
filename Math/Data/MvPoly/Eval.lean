import Math.Data.MvPoly.Defs
import Math.Algebra.Algebra.Hom
import Math.Algebra.Module.Hom

namespace MvPoly

section EvalWith

variable [SemiringOps P] [SemiringOps M] [FunLike F P M]
  [IsZeroHom F P M] [IsOneHom F P M] [IsAddHom F P M] [IsMulHom F P M]
  [IsSemiring P] [IsSemiring M] [IsCommMagma P] [IsCommMagma M]
  [DecidableEq σ]
  (f: F)

def evalVars (x: σ -> M) (p: Vars σ) : M :=
  p.toFinsupp.prod (fun i n => x i ^ n) <| by
    intro i h
    simp
    rw [h, npow_zero]

def evalWith (x: σ -> M) (p: MvPoly P σ) : M :=
  p.toFinsupp.sum (fun i p => f p * evalVars x i) (by
    intro i eq
    dsimp
    rw [eq, map_zero, zero_mul])

@[simp]
def evalWith_C (x: σ -> M) (a: P) : evalWith f x (C a) = f a := by
  unfold evalWith
  erw [Finsupp.single_sum]
  rw (occs := [2]) [←mul_one (f a)]
  rfl

@[simp]
def evalWith_monomial (x: σ -> M) (n: Vars σ) : evalWith f x (monomial n: MvPoly P σ) = evalVars x n := by
  unfold evalWith
  erw [Finsupp.single_sum, map_one, one_mul]

@[simp]
def evalVars_zero (x: σ -> M) : evalVars x 0 = 1 := by
  apply Finsupp.zero_prod

@[simp]
def evalVars_add (x: σ -> M) (a b: Vars σ) : evalVars x (a + b) = evalVars x a * evalVars x b := by
  unfold evalVars
  erw [Finsupp.add_prod]
  intro i a b
  rw [npow_add]

@[simp]
def evalVars_single (x: σ -> M) (i: σ) (n: ℕ) : evalVars x (AddMonoidAlgebra.single i n) = (x i) ^ n := by
  unfold evalVars
  erw [Finsupp.single_prod]

@[simp]
def evalWith_X (x: σ -> M) (i: σ) : evalWith f x (X i) = x i := by
  simp [X]

@[simp]
def evalWith_add (x: σ -> M) (a b: MvPoly P σ) : evalWith f x (a + b) = evalWith f x a + evalWith f x b := by
  apply Finsupp.add_sum
  intro i a b
  rw [map_add, add_mul]

@[simp]
def evalWith_mul_X (x: σ -> M) (a: MvPoly P σ) : evalWith f x (a * X i) = evalWith f x a * x i := by
  rw [mul_comm]
  rw [X, AddMonoidAlgebra.mul_def]
  unfold AddMonoidAlgebra.mul'
  rw [monomial]
  erw [Finsupp.single_sum]
  rw [evalWith]
  conv => {
    lhs; arg 1;
    rw [AddMonoidAlgebra.sum_toFinsupp (h₁ := by
      intro i h
      simp only
      rw [h, mul_zero ,AddMonoidAlgebra.single_zero]
      rfl)]
  }
  rw [Finsupp.sum_sum_index]
  conv => {
    arg 1; arg 2; intro a b
    simp; rw [Finsupp.single_sum]
    simp
    rw [mul_left_comm]
  }
  let g : M →+ M := {
    toFun a := x i * a
    map_zero := by simp
    map_add := by simp [mul_add]
  }
  show a.toFinsupp.sum (fun a b => g (f b * evalVars x a)) _ =
    evalWith f x a * x i
  rw [←Finsupp.map_sum (F := M →+ M) (γ := M) (γ' := M) _ _ g]
  rw [mul_comm]; rfl
  clear a i
  intro i a b
  rw [map_add, add_mul]
  intro i
  simp
  rfl
  intro i
  simp [map_zero]

@[simp]
def evalWith_mul (x: σ -> M) (a b: MvPoly P σ) : evalWith f x (a * b) = evalWith f x a * evalWith f x b := by
  let _smul := RingHom.toSMul (toRingHom f)
  have := RingHom.toIsModule (toRingHom f)
  induction a using alg_induction generalizing b with
  | add a b iha ihb => simp [add_mul, iha, ihb]
  | mul a₀ a₁ ih₀ ih₁ => rw [mul_assoc, ih₀, ih₁, ih₀, mul_assoc]
  | C =>
    simp
    rw [←smul_eq_C_mul, evalWith]
    erw [Finsupp.smul_sum]
    rfl
    intro vs p
    rw [map_mul, mul_assoc]
    rfl
  | X i =>
    rw [mul_comm, evalWith_mul_X]
    simp [X, mul_comm]

def evalWithHom (x: σ -> M) : MvPoly P σ →+* M where
  toFun := evalWith f x
  map_zero := rfl
  map_one := by rw [←map_one C, evalWith_C, map_one]
  map_add {x y} := by rw [evalWith_add]
  map_mul {x y} := by rw [evalWith_mul]

def evalWithHom_eq_evalWith : evalWithHom f x = evalWith (σ := σ) f x := rfl

end EvalWith

section Eval

variable [SemiringOps P] [SemiringOps A] [FunLike F P A]
  [IsSemiring P] [IsSemiring A] [IsCommMagma P] [IsCommMagma A]
  [DecidableEq σ] [SMul P A] [AlgebraMap P A] [IsAlgebra P A]

def eval (x: σ -> A) (p: MvPoly P σ) : A :=
  evalWith algebraMap x p

@[simp]
def eval_C (x: σ -> A) (a: P) : eval x (C a) = algebraMap a :=
  evalWith_C _ _ _

@[simp]
def eval_X (x: σ -> A) (i: σ) : eval (P := P) x (X i) = x i :=
  evalWith_X _ _ _

@[simp]
def eval_add (x: σ -> A) (a b: MvPoly P σ) : eval x (a + b) = eval x a + eval x b :=
  evalWith_add _ _ _ _

@[simp]
def eval_mul (x: σ -> A) (a b: MvPoly P σ) : eval x (a * b) = eval x a * eval x b :=
  evalWith_mul _ _ _ _

def evalHom (x: σ -> A) : MvPoly P σ →ₐ[P] A where
  toFun := eval x
  map_algebraMap := eval_C _
  map_add {x y} := by rw [eval_add]
  map_mul {x y} := by rw [eval_mul]

def evalHom_eq_eval : evalHom (σ := σ) (P := P) (A := A) x = eval (σ := σ) (P := P) (A := A) x := rfl

@[simp]
def evalHom_C (x: σ -> A) (a: P) : evalHom x (C a) = algebraMap a :=
  evalWith_C _ _ _

@[simp]
def evalHom_X (x: σ -> A) (i: σ) : evalHom (P := P) x (X i) = x i :=
  evalWith_X _ _ _

end Eval

noncomputable section Lift

variable [SemiringOps P] [IsSemiring P] [IsCommMagma P]
  [SemiringOps A] [IsSemiring A] [IsCommMagma A] [SMul P A] [AlgebraMap P A] [IsAlgebra P A]
  [SemiringOps B] [IsSemiring B] [IsCommMagma B] [SMul P B] [AlgebraMap P B] [IsAlgebra P B]
  -- [DecidableEq σ] [DecidableEq σ'] [DecidableEq σ'']
  [DecidableEq A] [DecidableEq B] [DecidableEq P]

@[irreducible]
-- show that MvPoly is the free commutative P-algebra over σ
def lift [DecidableEq σ] : (σ -> A) ≃ (MvPoly P σ →ₐ[P] A) where
  toFun := evalHom
  invFun x i := x (X i)
  leftInv f := by
    ext i
    simp
  rightInv f := by
    ext p
    simp
    induction p using alg_induction with
    | C p =>
      show _ = f (algebraMap p)
      rw [evalHom_C, map_algebraMap]
    | X i => simp
    | add a b iha ihb => simp [iha, ihb, map_add]
    | mul a b iha ihb => simp [iha, ihb, map_mul]


unseal lift in
@[simp] def apply_lift_C {deceq: DecidableEq σ} (x: σ -> A) (p: P) : lift x (C p) = algebraMap p := evalWith_C _ _ _
unseal lift in
@[simp] def apply_lift_X {deceq: DecidableEq σ} (x: σ -> A) : lift x (X i: MvPoly P σ) = x i := evalWith_X _ _ _

def lift_X {deceq: DecidableEq σ} (x: MvPoly P σ) : lift (X: σ -> MvPoly P σ) x = x := by
  induction x using alg_induction with
  | C a => rw [apply_lift_C]; rfl
  | X => rw [apply_lift_X]
  | add a b iha ihb => rw [map_add, iha, ihb]
  | mul a b iha ihb => rw [map_mul, iha, ihb]

def map [deceq: DecidableEq σ] [deceq': DecidableEq σ'] (f: σ -> σ') : MvPoly P σ →ₐ[P] MvPoly P σ' :=
  lift (fun x => MvPoly.X (f x))

@[simp] def apply_map_C {deceq: DecidableEq σ} {deceq': DecidableEq σ'} (f: σ -> σ') : map f (C x) = C (P := P) x := apply_lift_C _ _
@[simp] def apply_map_X {deceq: DecidableEq σ} {deceq': DecidableEq σ'} (f: σ -> σ') : map f (X i) = X (P := P) (f i) := apply_lift_X _

def map_map {deceq: DecidableEq σ} {deceq': DecidableEq σ'} {deceq'': DecidableEq σ''} (f: σ' -> σ'') (g: σ -> σ') (x: MvPoly P σ) : map f (map g x) = map (f ∘ g) x := by
  induction x using alg_induction with
  | add a b iha ihb => simp [map_add, iha, ihb]
  | mul a b iha ihb => simp [map_mul, iha, ihb]
  | C => simp
  | X => simp

def map_comp_map {deceq: DecidableEq σ} {deceq': DecidableEq σ'} {deceq'': DecidableEq σ''} (f: σ' -> σ'') (g: σ -> σ') : (map f).comp (map g) = map (f ∘ g) (P := P) := by
  apply DFunLike.ext
  apply map_map

def lift_id_map_X {deceq: DecidableEq σ} {h: DecidableEq (MvPoly P σ)} : lift (P := P) (A := MvPoly P σ) id (map (P := P) (σ := σ) (MvPoly.X (P := P)) x) = x := by
  induction x using alg_induction with
  | add a b iha ihb => simp [map_add, iha, ihb]
  | mul a b iha ihb => simp [map_mul, iha, ihb]
  | C => simp; rfl
  | X => simp

def lift_id_comp_map_X {deceq: DecidableEq σ} {h: DecidableEq (MvPoly P σ)} : (MvPoly.lift id).comp (MvPoly.map MvPoly.X) = AlgHom.id (MvPoly P σ) := by
  apply DFunLike.ext
  intro x
  apply lift_id_map_X

def lift_comp_map_algmap (f: A →ₐ[P] B) : (lift id).comp (map f) = f.comp (lift id) := by
  ext x;
  induction x using alg_induction with
  | add a b iha ihb => simp [map_add, iha, ihb]
  | mul a b iha ihb => simp [map_mul, iha, ihb]
  | C => simp; rw [map_algebraMap]
  | X => simp

-- def lift_lift (f: A -> B) (g: σ -> A) (x: MvPoly P σ) : (lift f) (lift g x) = lift (f ∘ g) x := by
--   induction x using alg_induction with
--   | C a => rw [apply_lift_C]; rfl
--   | X => rw [apply_lift_X]
--   | add a b iha ihb => rw [map_add, iha, ihb]
--   | mul a b iha ihb => rw [map_mul, iha, ihb]

end Lift

end MvPoly
