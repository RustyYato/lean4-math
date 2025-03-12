import Math.Data.Fintype.Algebra
import Math.Data.Fintype.Cases

namespace Fintype

def option_sigma_equiv_sum_sigma {β: Option α -> Type*} : (Σx: Option α, β x) ≃ β .none ⊕ Σx: α, β x where
  toFun
  | ⟨.none, b⟩ => .inl b
  | ⟨.some a, b⟩ => .inr ⟨a, b⟩
  invFun
  | .inl b => ⟨.none, b⟩
  | .inr ⟨a, b⟩ => ⟨.some a, b⟩
  leftInv x := by
    rcases x with ⟨a, b⟩
    cases a <;> rfl
  rightInv x := by cases x <;> rfl

def option_pi_equiv_prod_pi {β: Option α -> Type*} : (∀x: Option α, β x) ≃ β .none × ∀x: α, β x where
  toFun f := ⟨f _, fun _ => f _⟩
  invFun f x := match x with
     | .none => f.1
     | .some x => f.2 x
  leftInv f := by
    dsimp
    ext x
    cases x <;> rfl
  rightInv x := by cases x <;> rfl

def card_sigma {α: Type*} {β: α -> Type*} [ha: Fintype α] [hb: ∀x, Fintype (β x)] : card (Σx: α, β x) = ∑x: α, card (β x) := by
  induction ha using typeInduction with
  | empty => rfl
  | option α _ ih =>
    rw [sum_option, card_eq_of_equiv option_sigma_equiv_sum_sigma,
      card_sum]
    congr
    apply ih
  | eqv α' α eqv _ ih =>
    let eqv' := Fintype.ofEquiv' eqv
    have := @ih (β <| eqv ·) _
    apply Eq.trans _ (Eq.trans this _)
    apply card_eq_of_equiv
    refine Equiv.congrSigma ?_ ?_
    symm; assumption
    intro x
    rw [Equiv.symm_coe]
    refine sum_eq_of_equiv (ι₀ := α') (ι₁ := α) (α := Nat) _ _ eqv ?_
    intro i
    rfl

def card_prod {α: Type*} {β: Type*} [ha: Fintype α] [hb: Fintype β] : card (α × β) = card α * card β := by
  rw [card_eq_of_equiv (Equiv.prod_equiv_sigma _ _), card_sigma, sum_const]
  rfl

def card_pi {α: Type*} {β: α -> Type*} [dec: DecidableEq α] [ha: Fintype α] [hb: ∀x, Fintype (β x)] : card (∀x: α, β x) = ∏x: α, card (β x) := by
  classical
  revert β dec
  induction ha using typeInduction with
  | empty =>
    intro β _ _
    rfl
  | option α _ ih =>
    intro β _ hb
    rw [prod_option, card_eq_of_equiv option_pi_equiv_prod_pi,
      card_prod]
    congr
    apply ih
  | eqv α' α eqv _ ih =>
    intro β _ hb
    let eqv' := Fintype.ofEquiv' eqv
    have := @ih (β <| eqv ·) _
    apply Eq.trans _ (Eq.trans this _)
    apply card_eq_of_equiv
    refine Equiv.congrPi ?_ ?_
    symm; assumption
    intro x
    rw [Equiv.symm_coe]
    refine prod_eq_of_equiv (ι₀ := α') (ι₁ := α) (α := Nat) _ _ eqv ?_
    intro i
    rfl

def card_function {α: Type*} {β: Type*} [DecidableEq α] [ha: Fintype α] [hb: Fintype β] : card (α -> β) = card β ^ card α := by
  rw [card_pi, prod_const]

end Fintype
