import Math.Order.Defs
import Math.Data.Set.Basic

instance : IsPartialOrder (Set α) where
  lt_iff_le_and_not_le := Iff.rfl
  le_antisymm := Set.sub_antisymm
  le_refl := Set.sub_refl
  le_trans := Set.sub_trans
