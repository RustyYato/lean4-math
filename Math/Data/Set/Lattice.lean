import Math.Order.Lattice.Basic
import Math.Data.Set.Basic

instance : LE (Set α) where
  le a b := a ⊆ b
instance : LT (Set α) where
  lt a b := a ≤ b ∧ ¬b ≤ a

instance : IsPartialOrder (Set α) where
  lt_iff_le_and_not_le := Iff.rfl
  le_antisymm := Set.sub_antisymm
  le_refl := Set.sub_refl
  le_trans := Set.sub_trans

instance : Sup (Set α) where
  sup a b := a ∪ b
instance : Inf (Set α) where
  inf a b := a ∩ b

instance : IsLattice (Set α) where
  le_sup_left := Set.sub_union_left
  le_sup_right := Set.sub_union_right
  sup_le := by
    intro a b k ak bk
    intro x mem
    cases Set.mem_union.mp mem
    apply ak
    assumption
    apply bk
    assumption
  inf_le_left := Set.inter_sub_left
  inf_le_right := Set.inter_sub_right
  le_inf := by
    intro a b k ka kb x mem
    apply Set.mem_inter.mpr
    apply And.intro
    apply ka; assumption
    apply kb; assumption
