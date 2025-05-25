import Math.Data.«Fintype-old».Basic

namespace Fintype

def typeInduction {motive: ∀(α: Type*), Fintype α -> Prop}
  (empty: motive PEmpty inferInstance)
  (option: ∀α: Type _, (inst: Fintype α) -> motive α inst  -> motive (Option α) inferInstance)
  (eqv: ∀α β: Type _, ∀eqv: α ≃ β, (inst: Fintype α) -> motive α inst -> motive β (Fintype.ofEquiv' eqv))
  : ∀{α}, (inst: Fintype α) -> motive α inst := by
  intro α inst
  induction h:card α generalizing α with
  | zero =>
    rw [Subsingleton.allEq inst]
    apply eqv PEmpty
    have := Fintype.IsEmpty h
    exact Equiv.empty
    apply empty
  | succ n ih =>
    have ⟨β, ⟨eqv_optβ, _⟩⟩  := equiv_option h
    rw [Subsingleton.allEq inst]
    apply eqv
    symm; assumption
    apply option
    apply ih (inferInstanceAs (Fintype β))
    rw [←card_ofEquiv' eqv_optβ, card_option (inst := inferInstance)] at h
    rw [Nat.add_right_cancel_iff] at h
    assumption

end Fintype
