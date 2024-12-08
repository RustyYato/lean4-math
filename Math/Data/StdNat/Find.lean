import Math.Data.WellFounded.Basic

namespace Nat

variable {m n k : Nat} {p : Nat → Bool} (H: ∃n, p n)

private def rel (m n: Nat) : Prop := m = n + 1 ∧ ∀k ≤ n, ¬p k

private def wf : WellFounded (@rel p) := by
  let ⟨n, pn⟩ := H
  apply WellFounded.intro
  suffices ∀ m k, n ≤ k + m → Acc rel k from fun _ => this _ _ (Nat.le_add_left _ _)
  intro a
  induction a with
  | zero =>
    intro k n_le_k
    rw [Nat.add_zero] at n_le_k
    apply Acc.intro
    intro b r
    obtain ⟨h, g⟩ := r
    have := g _ n_le_k
    contradiction
  | succ a ih =>
    intro k n_le_ka
    rw [Nat.add_succ, ←Nat.succ_add] at n_le_ka
    apply Acc.intro
    intros b r
    apply ih
    cases r.left
    assumption

def findX : { n // p n ∧ ∀m < n, ¬p m } :=
  (wf H).fix (C := fun x => (∀m < x, ¬p m) -> { n // p n ∧ ∀m < n, ¬p m })
    (fun a ih h =>
      if pa: p a then
        ⟨a, pa, h⟩
      else
        have h :  ∀ (m : Nat), m ≤ a → ¬p m = true :=
          fun _ r₀ =>
            match r₀ with
            | .refl => pa
            | .step x_le => h _ (Nat.lt_of_le_of_lt x_le (Nat.lt_succ_self _))
        ih a.succ ⟨rfl, h⟩ (fun m r => h m (Nat.le_of_lt_succ r))) 0 nofun

def find : Nat := findX H
def find_spec : p (find H) := (findX H).property.left
def lt_find_spec : ∀m < (find H), ¬p m := (findX H).property.right

variable [DecidablePred P] (G: ∃n: Nat, P n)

private def cast_exists : (∃n, P n) -> ∃n, decide (P n)
| .intro x pn => ⟨x, decide_eq_true pn⟩

def findP := find (cast_exists G)
def findP_spec : P (findP G) := of_decide_eq_true (find_spec (cast_exists G))
def lt_findP_spec: ∀m < (findP G), ¬P m := fun m lt =>
  of_decide_eq_false <| Bool.eq_false_iff.mpr <| lt_find_spec (cast_exists G) m lt

end Nat
