import Math.Data.Poly.Basic

def Fin.foldl_id {f} (h: ∀a b, f a b = a) : Fin.foldl n f init = init := by
  induction n generalizing init with
  | zero => rw [Fin.foldl_zero]
  | succ b ih =>
    rw [Fin.foldl_succ, ih, h]
    intro a b
    rw [h]

namespace Poly

def fold [Zero α] (p: Poly α) (init: β) (f: α -> ℕ -> β -> β) (resp_zero: ∀n x, f 0 n x = x): β := by
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

def eval [SemiringOps α] [IsSemiring α] (p: Poly α) (x: α) : α :=
  p.fold 0 (fun a n s => s + a * x ^ n) <| by
    intro n x
    simp
    rw [zero_mul, add_zero]

end Poly
