import Math.Data.Countable.Card
import Math.Logic.Small.Basic

instance [IsCountable α] : Small.{u} α where
  exists_equiv := by
    rcases lt_or_eq_of_le (Cardinal.le_aleph₀_of_countable α) with h | h
    rw [Cardinal.lt_aleph₀] at h
    obtain ⟨n, h⟩ := h
    have ⟨h⟩ := Quotient.exact h
    exists ULift (Fin n)
    refine ⟨h.trans ?_⟩
    apply Equiv.congrULift
    rfl
    have ⟨h⟩ := Quotient.exact h
    exists ULift ℕ
    refine ⟨h.trans ?_⟩
    apply Equiv.congrULift
    rfl
