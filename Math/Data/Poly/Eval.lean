import Math.Data.Poly.Basic
import Math.Algebra.Hom.Defs
import Math.Algebra.Group.Hom

def Fin.foldl_id {f} (h: ∀a b, f a b = a) : Fin.foldl n f init = init := by
  induction n generalizing init with
  | zero => rw [Fin.foldl_zero]
  | succ b ih =>
    rw [Fin.foldl_succ, ih, h]
    intro a b
    rw [h]

section

variable {motive: ℕ -> ℕ -> Prop}
  (zero: motive 0 0)
  (succ_left: ∀n m, m ≤ n -> motive n m -> motive (n + 1) m)
  (succ_right: ∀n m, n ≤ m -> motive n m -> motive n (m + 1))
  (succ: ∀n, motive n n -> motive (n + 1) (n + 1))

def nat_ind₂: ∀n m, motive n m
| 0, 0 => zero
| 0, m + 1 => succ_right 0 m (Nat.zero_le _) (nat_ind₂ _ _)
| n + 1, 0 => succ_left n 0 (Nat.zero_le _) (nat_ind₂ _ _)
| n + 1, m + 1 =>
  match lt_trichotomy n m with
  | .inl h => succ_right (n + 1) m (Nat.le_of_lt_succ (Nat.succ_lt_succ h)) (nat_ind₂ _ _)
  | .inr (.inl h) => h ▸ succ n (nat_ind₂ _ _)
  | .inr (.inr h) => succ_left n (m + 1) (Nat.le_of_lt_succ (Nat.succ_lt_succ h)) (nat_ind₂ _ _)

end

def Nat.max_succ_left (n m: Nat) (h: m ≤ n) : max (n + 1) m = max n m + 1 := by
  rw [max_def, max_def, if_neg]
  split
  congr; apply Nat.le_antisymm <;> assumption
  rfl
  rw [not_le, Nat.lt_succ]
  assumption

def Nat.max_succ_right (n m: Nat) (h: n ≤ m) : max n (m + 1) = max n m + 1 := by
  rw [max_comm, max_succ_left, max_comm]
  assumption

namespace Poly

def foldl' [Zero P] (bound: ℕ) (p: ℕ -> P) (init: S) (f: P -> ℕ -> S -> S): S := Fin.foldl (n := bound) (fun x n => f (p n.val) n.val x) init

def foldl'_zero [Zero P] {p: ℕ -> P} : foldl' 0 p init f = init := rfl
def foldl'_succ [Zero P] {p: ℕ -> P} : foldl' (n + 1) p init f = foldl' n (p ∘ Nat.succ) (f (p 0) 0 init) (fun p n s => f p (n + 1) s) := by
  unfold foldl'
  rw [Fin.foldl_succ]
  rfl
def foldl'_succ' [Zero P] {p: ℕ -> P} {init: S} : foldl' (n + 1) p init f = f (p n) n (foldl' n p init f) := by
  unfold foldl'
  rw [Fin.foldl_succ_last]
  rfl
def foldl'_eq [Zero P] (p q: ℕ -> P) {init: S} :
  (∀x < n, p x = q x) ->
  foldl' n p init f = foldl' n q init f := by
  intro h
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [foldl'_succ', foldl'_succ', ih, h]
    apply Nat.lt_succ_self
    intro x hx
    apply h
    apply Nat.lt_trans hx
    apply Nat.lt_succ_self

private def strip [Zero P] (p: ℕ -> P) (bound: ℕ) : ℕ -> P :=
  fun n => if n > bound then 0 else p n

private def strip_succ [Zero P] (p: ℕ -> P) (bound: ℕ) : strip (p ∘ Nat.succ) bound = (strip p (bound+1)) ∘ Nat.succ := by
  unfold Poly.strip
  ext i
  simp [Poly.strip]

private def strip_add [Zero P] [Add P] [IsAddZeroClass P] (p q: ℕ -> P) (bound: ℕ) :
  strip (fun n => p n + q n) bound = fun n => strip p bound n + strip q bound n := by
  unfold Poly.strip
  ext i
  split
  rw [add_zero]
  rfl

def strip_eq_of_deg_le [Zero P] (p: ℕ -> P) (bound bound': ℕ) :
  Poly.DegreeLe p bound' ->
  bound' ≤ bound ->
  strip p bound = p := by
  intro deg h
  unfold Poly.strip
  ext i
  split <;> rename_i g
  rw [deg]
  apply lt_of_le_of_lt h g
  rfl

private def foldl'_eq_strip [Zero P] (p: ℕ -> P) {init: S} :
  foldl' n p init f = foldl' n (strip p n) init f := by
  rw [foldl'_eq]
  intro x hx
  rw [Poly.strip, if_neg]
  exact Nat.not_lt_of_gt hx

def foldl'_sum [Zero P] [Zero S] [Add S] [IsAddZeroClass S] [IsAddSemigroup S] (p: ℕ -> P) (f: P -> ℕ -> S) :
  foldl' n p 0 (fun p n s => s + f p n) = Fin.sum (fun x: Fin n => f (p x.val) x.val) := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    rw [foldl'_succ', Fin.sum_succ, ih]
    rfl

def foldl [Zero P] (p: P[X]) (init: S) (f: P -> ℕ -> S -> S) (resp_zero: ∀n x, f 0 n x = x): S := by
  apply Quot.liftOn p.has_degree _ _
  intro ⟨bound, spec⟩
  refine foldl' (bound+1) p.coeffs init f
  intro ⟨a, bound_a⟩ ⟨b, bound_b⟩ _
  dsimp
  match p with
  | .mk p h =>
  dsimp [foldl']
  dsimp at bound_a bound_b
  clear h
  induction a generalizing f p b init with
  | zero =>
    rw [Fin.foldl_succ, Fin.foldl_zero, Fin.foldl_succ]
    cases b with
    | zero => rw [Fin.foldl_zero]
    | succ b =>
      simp
      generalize f (p 0) 0 init = px
      conv => {
        rhs; arg 2;
        intro x i
        rw [bound_a _ (Nat.zero_lt_succ _), resp_zero]
      }
      rw [Fin.foldl_succ, Fin.foldl_id]
      intros; rfl
  | succ a ih =>
    rw [Fin.foldl_succ]
    cases b with
    | zero =>
      simp
      conv => {
        lhs; arg 2;
        intro x i
        rw [bound_b _ (Nat.zero_lt_succ _), resp_zero]
      }
      rw [Fin.foldl_id, Fin.foldl_succ, Fin.foldl_zero]
      intros; rfl
    | succ b =>
      rw [Fin.foldl_succ (n := b + 1)]
      simp
      apply ih (f (p 0) 0 init) (fun a n x => f a (n + 1) x) _ b (p ∘ Nat.succ)
      · intro n h
        apply bound_a
        apply Nat.succ_lt_succ
        assumption
      · intro n h
        apply bound_b
        apply Nat.succ_lt_succ
        assumption
      · intro n x
        simp
        rw [resp_zero]

section

variable [SemiringOps S] [IsSemiring S]

-- evaluate this polynomial when given a zero homomorphism from
-- the coeffiecients to the output semiring
-- normally, this would be a ring homomorphism from a semiring to a semiring
-- but we don't need all those restrictions
def evalWith [FunLike F P S] [Zero P] [IsZeroHom F P S]
  (p: P[X]) (f: F) (x: S) : S :=
  p.foldl 0 (fun a n s => s + f a * x ^ n) (by
    intro n x
    simp
    rw [resp_zero, zero_mul, add_zero])

-- evaluate this polynomial in module over P
def eval [SemiringOps P] [IsSemiring P] [SMul P S] [IsModule P S] (p: P[X]) (x: S) : S :=
  p.foldl 0 (fun a n s => s + a • x ^ n) <| by
    intro n x
    simp
    rw [zero_smul, add_zero]

-- over an algebra, eval and evalWith algebraMap coincide
def eval_eq_evalWith [SemiringOps P] [SMul P S] [AlgebraMap P S] [IsAlgebra P S] (p: P[X]) (x: S) : p.eval x = p.evalWith algebraMap x := by
  unfold eval evalWith
  congr
  ext c n s
  rw [smul_def]

end

section
variable [Zero P] {init: S} {f: P -> ℕ -> S -> S} {resp_zero: ∀n x, f 0 n x = x}

def foldl_const (a: P) : Poly.foldl (Poly.const a) init f resp_zero = f a 0 init := rfl
def foldl_mul_var (a: P[X]) : Poly.foldl a.mul_var init f resp_zero = Poly.foldl a init (fun a n s => f a (n + 1) s) (by
    intro n x
    simp
    rw [resp_zero]) := by
  match a with
  | .mk a ha =>
  cases ha using Quot.ind with | mk ha =>
  obtain ⟨bound, ha⟩ := ha
  unfold mul_var foldl
  show foldl' _ _ _ _ = foldl' _ _ _ _
  unfold foldl'
  rw [Fin.foldl_succ]
  simp
  rw [resp_zero]

@[simp]
def foldl_mk (p: ℕ -> P) (deg: Nat) (isdeg: Poly.DegreeLe p deg) :
  Poly.foldl ⟨p, Squash.mk ⟨deg, isdeg⟩⟩ init f resp_zero = Poly.foldl' (deg+1) p init f  := rfl

def foldl'_add [Zero S] [Add S] [IsAddSemigroup S] [IsAddZeroClass S] (f: P -> ℕ -> S) :
  foldl' bound p init (fun p n s => s + f p n) = init + foldl' bound p 0 (fun p n s => s + f p n) := by
  induction bound generalizing init f p with
  | zero => simp [foldl'_zero, add_zero]
  | succ n ih =>
    simp [foldl'_succ]
    rw [ih (init := init + _), ih (init := (f _ _)), add_assoc]

def foldl'_add_succ [Zero S] [Add S] [IsAddSemigroup S] [IsAddZeroClass S] (f: P -> ℕ -> S) :
  foldl' (bound + 1) p 0 (fun p n s => s + f p n) =
  foldl' bound p 0 (fun p n s => s + f p n) + f (p bound) bound := by
  rw [foldl', Fin.foldl_succ_last]
  rfl

end

section

variable [SemiringOps P] [SemiringOps S] [FunLike F P S]
  [IsZeroHom F P S] [IsOneHom F P S] [IsAddHom F P S] [IsMulHom F P S]
  [IsSemiring P] [IsSemiring S]
  (f: F)

@[simp]
def evalWith_const (p: P) (x: S) : (C p).evalWith f x = f p := by
  apply (foldl_const _).trans
  rw [npow_zero, mul_one, zero_add]

@[simp]
def evalWith_mul_var (p: P[X]) (x: S) : (mul_var p).evalWith f x = p.evalWith f x * x := by
  apply (foldl_mul_var _).trans
  rw [evalWith]
  match p with
  | .mk p hp =>
  cases hp using Squash.ind with | h deg =>
  obtain ⟨deg, hp⟩ := deg
  rw [foldl_mk, foldl_mk, foldl'_sum, foldl'_sum, Fin.sum_mul]
  congr; ext i
  rw [mul_assoc, npow_succ]

@[simp]
def evalWith_mul_X (p: P[X]) (x: S) : (p * X).evalWith f x = p.evalWith f x * x := by
  simp [mul_X]

@[simp]
def evalWith_add (p q: P[X]) (x: S) : (p + q).evalWith f x = p.evalWith f x + q.evalWith f x := by
  match p, q with
  | .mk p hp, .mk q hq =>
  induction hp using Squash.ind with | h hp =>
  induction hq using Squash.ind with | h hq =>
  obtain ⟨deg_p, hp⟩ := hp
  obtain ⟨deg_q, hq⟩ := hq
  unfold evalWith
  rw [foldl_mk, foldl_mk]
  apply (foldl_mk _ _ _).trans
  simp [foldl'_sum]
  rw [Fin.sum_extend (n := deg_p + 1) (m := max deg_p deg_q + 1),
    Fin.sum_extend (n := deg_q + 1) (m := max deg_p deg_q + 1),
    Fin.sum_add_sum_pairwise]
  congr; ext ⟨i, hi⟩
  simp;
  split <;> split <;> rename_i h g
  rw [resp_add, add_mul]
  rw [hq, add_zero, add_zero]
  omega
  rw [hp, zero_add, zero_add]
  omega
  rw [hp, hq, zero_add, resp_zero, zero_mul, add_zero]
  all_goals omega

@[simp]
def evalWith_mul [IsCommMagma S] (p q: P[X]) (x: S) : (p * q).evalWith f x = p.evalWith f x * q.evalWith f x := by
  induction p generalizing q with
  | const p =>
    induction q with
    | const q =>
      rw [←resp_mul]; simp
      rw [resp_mul]
    | mul_add q qs _ ih₀ ih₁ =>
      rw [mul_add]
      simp [ih₀, ih₁, ←mul_assoc]
      rw [mul_assoc, mul_add]
  | mul_add p ps _ ih₀ ih₁ =>
    simp [add_mul, mul_add, mul_assoc]
    simp [ih₀, ih₁, X_mul_eq_mul_X, mul_comm x]

def evalWith_zero : (0: P[X]).evalWith f (x: S) = 0 := by
  rw [←resp_zero C, evalWith_const, resp_zero]

def evalWith_one : (1: P[X]).evalWith f (x: S) = 1 := by
  erw [evalWith_const, resp_one]

def evalWithHom [IsCommMagma S] (x: S) : P[X] →+* S where
  toFun := (evalWith · f x)
  resp_zero := evalWith_zero _
  resp_one := evalWith_one _
  resp_add := evalWith_add _ _ _ _
  resp_mul := evalWith_mul _ _ _ _

def lift [IsCommMagma S] : P[X] →+* S[X] := evalWithHom (constHom.toRingHom.comp (toRingHom f)) X

end

section

variable [SemiringOps P] [SemiringOps S] [IsSemiring P] [IsSemiring S] [SMul P S] [AlgebraMap P S] [IsAlgebra P S]

@[simp]
def eval_const (p: P) (x: S) : (C p).eval x = algebraMap p := by
  simp [eval_eq_evalWith]

@[simp]
def eval_mul_X (p: P[X]) (x: S) : (p * X).eval x = p.eval x * x := by
  simp [eval_eq_evalWith]

@[simp]
def eval_add (p q: P[X]) (x: S) : (p + q).eval x = p.eval x + q.eval x := by
  simp [eval_eq_evalWith]

@[simp]
def eval_mul [IsCommMagma S] (p q: P[X]) (x: S) : (p * q).eval x = p.eval x * q.eval x := by
  simp [eval_eq_evalWith]

@[simp]
def eval_zero : (0: P[X]).eval (x: S) = 0 := by
  rw [←resp_zero C, eval_const, resp_zero]

@[simp]
def eval_one : (1: P[X]).eval (x: S) = 1 := by
  erw [eval_const, resp_one]

@[simp]
def eval_X [IsCommMagma S] (x: S) : (X: P[X]).eval x = x := by
  rw [←one_mul X, eval_mul_X]
  simp

def evalHom [IsCommMagma S] (x: S) : P[X] →+* S where
  toFun := (eval · x)
  resp_zero := eval_zero
  resp_one := eval_one
  resp_add := eval_add _ _ _
  resp_mul := eval_mul _ _ _

def evalHom_def [IsCommMagma S] (p: P[X]) (x: S) : evalHom x p = p.eval x := rfl

-- def of_eval_eq_zero [IsCommMagma P] (p: P[X]) : (∀x: P, p.eval x = 0) -> p = 0 := by
--   intro h
--   induction p with
--   | const p =>
--     have := h 0
--     rw [eval_const] at this
--     rw [zero_eq_const]
--     congr
--   | mul_add p ps ps_ne_zero ih₀ ih₁ =>
--     conv at h => {
--       intro x ; rw [eval_add, eval_mul_var, eval_const]
--     }
--     replace h : ∀x: P, ps.eval x * x + p = 0 := h
--     have := h 0
--     rw [mul_zero, zero_add] at this
--     subst this
--     rw [←zero_eq_const, add_zero]
--     rw [ih₀]
--     sorry
--     intro x
--     conv at h => { intro; rw [add_zero] }
--     sorry

end

section

variable [SemiringOps P] [IsSemiring P] [IsCommMagma P]

def compHom : P[X] -> P[X] →+* P[X] := evalHom (S := P[X])
def comp : P[X] -> P[X] -> P[X] := fun x y => compHom y x

@[simp]
def compHom_const (p: P) (q: P[X]) : q.compHom (C p) = C p := by
  rw [compHom, evalHom_def, eval_const]
  rfl

@[simp]
def comp_mul_X (p q: P[X]) : q.compHom (p * X) = q.compHom p * q := by
  rw [compHom, evalHom_def, eval_mul_X]
  rfl

def eval_compHom (p q: P[X]) : (p.compHom q).eval x = q.eval (p.eval x (S := P)) := by
  induction q with
  | const q => simp
  | mul_add q qs ps_ne_zero ih₀ ih₁ => simp [ih₀, ih₁, resp_add]

def eval_comp (p q: P[X]) : (p.comp q).eval x = p.eval (q.eval x (S := P)) :=
  eval_compHom _ _

end

-- instance [RingOps P] [IsRing P] [IsCommMagma P] : FunLike P[X] P P where
--   coe := eval
--   coe_inj := by
--     intro a b eq
--     rcases subsingleton_or_nontrivial P with subsing | nontriv
--     apply Subsingleton.allEq
--     apply eq_of_sub_eq_zero
--     have : ∀x: P, (a - b).eval x = 0 := by
--       intro x
--       show evalHom x (a - b) = 0
--       rw [resp_sub]
--       show a.eval x - b.eval x = 0
--       rw [eq, sub_self]
--     exact of_eval_eq_zero _ this

end Poly
