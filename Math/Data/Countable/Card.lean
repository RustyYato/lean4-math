import Math.Data.Cardinal.Basic
import Math.Data.Countable.Basic

namespace Cardinal

def le_aleph₀_of_countable (α: Type*) [h: IsCountable α] : #α ≤ ℵ₀ := by
  have ⟨h⟩ := h
  refine ⟨h.trans (Equiv.ulift _).symm.toEmbedding⟩

end Cardinal
