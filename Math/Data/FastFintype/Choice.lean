import Math.Data.FastFintype.Defs
import Math.Data.Setoid.Basic

variable {ι : Type*} [fι: Fintype ι] [DecidableEq ι]

@[match_pattern]
private def finsucc (x: Fin n) : Fin (n + 1) := ⟨x.val + 1, by omega⟩

def Fin.choice {α : Fin n → Sort*} {S : ∀i, Setoid (α i)} (q: ∀i: Fin n, Quotient (S i)) :
  Quotient (Setoid.forallSetoid α) :=
  match n with
  | 0 => Quotient.mk _ <| fun i => i.elim0
  | n + 1 =>
    (Fin.choice (fun i => q i.succ)).liftOn₂ (q 0)
      (fun fs f0 =>
        Quotient.mk _ <| fun i =>
        match i with
        | 0 => f0
        | ⟨i + 1, hi⟩ => fs ⟨i, Nat.lt_of_succ_lt_succ hi⟩) <| by
      intro f₀ a₀ f₁ a₁ feq aeq
      simp
      apply Quotient.sound
      intro i
      cases i using Fin.cases
      assumption
      apply feq
