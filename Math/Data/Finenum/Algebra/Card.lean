import Math.Data.Finenum.Algebra.Monoid
import Math.Data.Finenum.Impls.Sigma
import Math.Data.Finenum.Impls.Pi

namespace Finenum

@[simp]
def card_sigma' {α: ι -> Type*} {fι: Finenum ι} {fα: ∀i, Finenum (α i)} {f: Finenum (Σi, α i)} : card (Σi, α i) = ∑i, card (α i) := by
  induction fι with
  | empty => simp
  | option ι ih =>
    simp
    rw [card_eq_of_equiv (Equiv.option_sigma_equiv_sum_sigma (α := ι) (β := α)),
      card_sum, ih]
  | eqv ι₀ ι₁ h ih =>
     rw [card_eq_of_equiv (Equiv.congrSigma (β₁ := fun i => α (h i)) h.symm ?_), ih]
     rw [sum_eqv h]
     intro i
     simp; rfl

def card_sigma {α: ι -> Type*} [Finenum ι] [∀i, Finenum (α i)] [Finenum (Σi, α i)] : card (Σi, α i) = ∑i, card (α i) := by
  apply card_sigma'

@[simp]
def card_pi' {α: ι -> Type*} {fι: Finenum ι} {fα: ∀i, Finenum (α i)} {f: Finenum (∀i, α i)} : card (∀i, α i) = ∏i, card (α i) := by
  classical
  induction fι with
  | empty => simp
  | option ι ih =>
    simp
    rw [card_eq_of_equiv Equiv.option_pi_equiv_prod_pi, card_prod, ih]
  | eqv ι₀ ι₁ h ih =>
    rw [card_eq_of_equiv (Equiv.congrPi (β₁ := fun i => α (h i)) h.symm ?_), ih]
    rw [prod_eqv h]
    intro i
    simp; rfl

def card_pi {α: ι -> Type*} [fι: Finenum ι] [fα: ∀i, Finenum (α i)] [f: Finenum (∀i, α i)] : card (∀i, α i) = ∏i, card (α i) := by
  apply card_pi'

@[simp]
def card_function' {fα: Finenum α} {fα: Finenum β} {f: Finenum (α -> β)} : card (α -> β) = card β ^ card α := by
  rw [card_pi, prod_const]
def card_function [fα: Finenum α] [fα: Finenum β] [f: Finenum (α -> β)] : card (α -> β) = card β ^ card α := by
  apply card_function'

end Finenum
