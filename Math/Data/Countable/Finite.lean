import Math.Data.Countable.Basic
import Math.Type.Finite

instance [h: IsFinite α] : IsCountable α := .intro (Equiv.congrEmbed (h.toEquiv) .rfl Fin.embedNat)
