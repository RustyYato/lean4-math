import Math.Data.Countable.Basic
import Math.Type.Finite

instance [h: IsFinite α] : IsCountable α := .intro (Fin.embedNat.congr (h.toEquiv).symm .refl)
