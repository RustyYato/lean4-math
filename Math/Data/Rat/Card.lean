import Math.Data.Countable.Card
import Math.Data.Rat.Encodable

def card_rat : #ℚ = ℵ₀ := by
  apply le_antisymm
  apply Cardinal.le_aleph₀_of_countable
  refine ⟨?_⟩
  exact {
    toFun n := n.down
    inj' := HasChar.natCast_inj.comp (Equiv.ulift _).inj
  }
