import Math.Data.Trunc
import Math.Data.Quotient.Basic
import Math.Logic.Nontrivial
import Math.Logic.Equiv.Basic

unsafe def Quotient.cilift
  {α: ι -> Sort u}
  {s: ∀i, Setoid (α i)}
  (f: (∀i, α i) -> β)
  (_resp: ∀g₀ g₁: ∀i, α i, (∀x, g₀ x ≈ g₁ x) -> f g₀ = f g₁):
  (∀i, Quotient (s i)) -> β := fun h => f (fun i => (h i).lift id lcProof)

@[implemented_by Quotient.cilift]
noncomputable def Quotient.ilift'
  {α: ι -> Sort u}
  {s: ∀i, Setoid (α i)}
  (f: (∀i, α i) -> β)
  (_resp: ∀g₀ g₁: ∀i, α i, (∀x, g₀ x ≈ g₁ x) -> f g₀ = f g₁):
  (∀i, Quotient (s i)) -> β := fun h => f (fun i => (h i).out)

def choice {α: ι -> Sort*} [S: ∀i, Setoid (α i)] (f: ∀i, Quotient (S i)): Quotient (Setoid.forallSetoid α) := by
  apply Quotient.ilift' (ι := ι) (α := α) (s := S) (β := Quotient (Setoid.forallSetoid α)) ?_ ?_
  assumption
  exact Quotient.mk _
  intro a b eq
  apply Quot.sound
  assumption

def exoticInstance : Decidable True := by
  apply @Quot.recOnSubsingleton _ _ (fun _ => Decidable True)
  -- lift the identity function
  exact (@choice (Trunc Bool) (fun _ => Bool) (fun _ => Setoid.trueSetoid _) id)
  intro f
  replace f: Trunc Bool -> Bool := f
  -- since Trunc is subsingleton, f can only take on one value
  -- but we lifted the identity function, which takes on two values
  apply decidable_of_iff (f (Trunc.mk false) = f (Trunc.mk true))
  simp
  congr 1
  apply Subsingleton.allEq

example : @decide True exoticInstance = true  := .trans (by congr) (decide_true _)
example : @decide True exoticInstance = false := by native_decide

#eval exoticInstance
