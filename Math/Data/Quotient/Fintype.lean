import Math.Data.Fintype.Basic
import Math.Data.Quotient.Basic

private
def Quotient.flift' {s: Setoid α} [DecidableEq ι]
  (xs: List ι)
  (f: (∀x, x ∈ xs -> α) -> β)
  (resp: ∀g₀ g₁: (∀x ∈ xs, α), (∀x h, g₀ x h ≈ g₁ x h) -> f g₀ = f g₁)
  (f': ∀x ∈ xs, Quotient s): β :=
  match xs with
  | [] => f fun x h => by contradiction
  | x::xs => by
    apply (f' x (List.Mem.head _)).lift _ _
    intro y
    apply Quotient.flift' xs _ _
    intro z mem
    exact f' z (List.Mem.tail _ mem)
    intro f₁
    apply f
    intro z hz
    if x = z then
      exact y
    else
      apply f₁ z
      cases hz
      contradiction
      assumption
    · intro g₀ g₁ eq
      apply resp
      intro z hz
      split
      apply Setoid.iseqv.refl
      apply eq
    · intro a b eq
      suffices (fun f₁: ∀x ∈ xs, α => f fun z hz => if h : x = z then a else f₁ z _) =
        (fun f₁: ∀x ∈ xs, α => f fun z hz => if h : x = z then b else f₁ z _) by
        conv => {
          lhs; arg 0; arg 2
          rw [this]
        }
      ext f₀
      apply resp
      intro z hz
      split
      assumption
      apply Setoid.iseqv.refl


def Quotient.flift {s: Setoid α} [fι: Fintype ι] [DecidableEq ι]
  (f: (ι -> α) -> β)
  (resp: ∀g₀ g₁: ι -> α, (∀x, g₀ x ≈ g₁ x) -> f g₀ = f g₁):
  (ι -> Quotient s) -> β := by
  intro h
  apply Quotient.flift' fι.all _ _
  intro x _
  exact h x
  intro x
  apply f
  intro y
  apply x y
  apply Fintype.complete
  intro g₀ g₁ eq
  apply resp
  intro x
  apply eq

private
def Quotient.mk_flift' {s: Setoid α} [DecidableEq ι]
  (xs: List ι)
  (f: (∀x, x ∈ xs -> α) -> β)
  (resp: ∀g₀ g₁: (∀x ∈ xs, α), (∀x h, g₀ x h ≈ g₁ x h) -> f g₀ = f g₁)
  (h: ∀x ∈ xs, α):
  Quotient.flift' xs f resp (fun x g => Quotient.mk s (h x g)) = f h := by
  induction xs with
  | nil =>
    unfold Quotient.flift'
    congr
    ext
    contradiction
  | cons x xs ih =>
    rw [Quotient.flift']
    rw [Quotient.mk_lift, ih]
    apply resp
    intro z hz
    dsimp
    split
    subst z
    apply Setoid.iseqv.refl
    apply Setoid.iseqv.refl

def Quotient.mk_flift {s: Setoid α} [fι: Fintype ι] [DecidableEq ι]
  (f: (ι -> α) -> β)
  (resp: ∀g₀ g₁: ι -> α, (∀x, g₀ x ≈ g₁ x) -> f g₀ = f g₁)
  (h: ι -> α):
  Quotient.flift f resp (fun x => Quotient.mk s (h x)) = f h := by
  apply Quotient.mk_flift'
