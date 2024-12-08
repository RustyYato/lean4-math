import Math.Data.WellFounded.Basic
import Math.Data.Nat.Order

namespace nat

variable {m n k : nat} {p : nat → Bool} (H: ∃n, p n)

private def rel (m n: nat) : Prop := m = n.succ ∧ ∀k ≤ n, ¬p k

private def wf : WellFounded (@rel p) := by
  let ⟨n, pn⟩ := H
  apply WellFounded.intro
  suffices ∀ m k, n ≤ k + m → Acc rel k from fun _ => this _ _ (nat.le_add_left _ _)
  intro a
  induction a using nat.rec with
  | zero =>
    intro k n_le_k
    rw [nat.add_zero] at n_le_k
    apply Acc.intro
    intro b r
    obtain ⟨h, g⟩ := r
    have := g _ n_le_k
    contradiction
  | succ a ih =>
    intro k n_le_ka
    rw [nat.add_succ, ←nat.succ_add] at n_le_ka
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
        have h :  ∀ (m : nat), m ≤ a → ¬p m = true := by
          intro _ r₀
          cases lt_or_eq_of_le r₀
          apply h
          assumption
          subst a
          assumption
        ih a.succ ⟨rfl, h⟩ (fun m r => h m (nat.le_of_lt_succ r))) 0 nofun

def find : nat := findX H
def find_spec : p (find H) := (findX H).property.left
def lt_find_spec : ∀m < (find H), ¬p m := (findX H).property.right

variable [DecidablePred P] (G: ∃n: nat, P n)

private def cast_exists : (∃n, P n) -> ∃n, decide (P n)
| .intro x pn => ⟨x, decide_eq_true pn⟩

def findP := find (cast_exists G)
def findP_spec : P (findP G) := of_decide_eq_true (find_spec (cast_exists G))
def lt_findP_spec: ∀m < (findP G), ¬P m := fun m lt =>
  of_decide_eq_false <| Bool.eq_false_iff.mpr <| lt_find_spec (cast_exists G) m lt

end nat
