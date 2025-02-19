import Math.Data.Poly.Basic
import Math.Algebra.Hom.Defs

def Fin.foldl_id {f} (h: ∀a b, f a b = a) : Fin.foldl n f init = init := by
  induction n generalizing init with
  | zero => rw [Fin.foldl_zero]
  | succ b ih =>
    rw [Fin.foldl_succ, ih, h]
    intro a b
    rw [h]

namespace Poly

def foldl [Zero P] (p: P[X]) (init: S) (f: P -> ℕ -> S -> S) (resp_zero: ∀n x, f 0 n x = x): S := by
  apply Quot.liftOn p.has_degree _ _
  intro ⟨bound, spec⟩
  refine Fin.foldl (n := bound + 1) (fun x n => f (p.coeffs n.val) n.val x) init
  intro ⟨a, bound_a⟩ ⟨b, bound_b⟩ _
  dsimp
  cases p with
  | mk  p h =>
  dsimp
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

end Poly
