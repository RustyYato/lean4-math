import Math.Data.Fintype.Basic
import Math.Data.Quotient.Basic

private
def Quotient.flift'
  {α: ι -> Sort*}
  {s: ∀i, Setoid (α i)} [DecidableEq ι]
  (xs: List ι)
  (f: (∀x, x ∈ xs -> α x) -> β)
  (resp: ∀g₀ g₁: (∀x ∈ xs, α x), (∀x h, g₀ x h ≈ g₁ x h) -> f g₀ = f g₁)
  (f': ∀x ∈ xs, Quotient (s x)): β :=
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
    if h:x = z then
      exact h ▸ y
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
      suffices (fun f₁: ∀x ∈ xs, α x => f fun z hz => if h : x = z then h ▸ a else f₁ z _) =
        (fun f₁: ∀x ∈ xs, α x => f fun z hz => if h : x = z then h ▸ b else f₁ z _) by
        conv => {
          lhs; arg 0; arg 2
          rw [this]
        }
      ext f₀
      apply resp
      intro z hz
      split
      rename_i hx
      subst x
      assumption
      apply Setoid.iseqv.refl

def Quotient.flift
  {α: ι -> Sort*}
  {s: ∀i, Setoid (α i)} [fι: Fintype ι] [DecidableEq ι]
  (f: (∀i, α i) -> β)
  (resp: ∀g₀ g₁: ∀i, α i, (∀x, g₀ x ≈ g₁ x) -> f g₀ = f g₁):
  (∀i,Quotient (s i)) -> β := by
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
def Quotient.mk_flift'
  {α: ι -> Sort*}
  {s: ∀i, Setoid (α i)} [DecidableEq ι]
  (xs: List ι)
  (f: (∀x, x ∈ xs -> α x) -> β)
  (resp: ∀g₀ g₁: (∀x ∈ xs, α x), (∀x h, g₀ x h ≈ g₁ x h) -> f g₀ = f g₁)
  (h: ∀x ∈ xs, α x):
  Quotient.flift' xs f resp (fun x g => Quotient.mk (s x) (h x g)) = f h := by
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

def Quotient.mk_flift
  {α: ι -> Sort*}
  {s: ∀i, Setoid (α i)} [fι: Fintype ι] [DecidableEq ι]
  (f: (∀i, α i) -> β)
  (resp: ∀g₀ g₁: ∀i, α i, (∀x, g₀ x ≈ g₁ x) -> f g₀ = f g₁)
  (h: ∀i, α i):
  Quotient.flift f resp (fun x => Quotient.mk (s _) (h x)) = f h := by
  apply Quotient.mk_flift'

def Quotient.flift_eq_ilift
  {α: ι -> Sort*} {s: ∀i, Setoid (α i)} [fι: Fintype ι] [DecidableEq ι]
  (f: (∀i, α i) -> β)
  (resp: ∀g₀ g₁: ∀i, α i, (∀x, g₀ x ≈ g₁ x) -> f g₀ = f g₁): flift f resp = ilift f resp := by
  ext g
  induction g using iind with | mk g =>
  rw [mk_flift, mk_ilift]
