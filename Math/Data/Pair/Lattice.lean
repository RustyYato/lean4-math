import Math.Data.Pair.Basic
import Math.Order.Lattice.Basic

variable [LE α] [LE β] [LT α] [LT β] [Max α] [Max β] [Min α] [Min β]

instance : Max (α × β) where
  max x y := (x.1 ⊔ y.1, x.2 ⊔ y.2)
instance : Min (α × β) where
  min x y := (x.1 ⊓ y.1, x.2 ⊓ y.2)

instance  [Max α] [Max β] [IsSemiLatticeMax α] [IsSemiLatticeMax β] : IsSemiLatticeMax (α × β) where
  le_max_left _ _ := ⟨le_max_left _ _, le_max_left _ _⟩
  le_max_right _ _ := ⟨le_max_right _ _, le_max_right _ _⟩
  max_le ha hb := ⟨max_le ha.left hb.left, max_le ha.right hb.right⟩

instance  [Max α] [Max β] [IsSemiLatticeMin α] [IsSemiLatticeMin β] : IsSemiLatticeMin (α × β) :=
  inferInstanceAs (IsSemiLatticeMin (αᵒᵖ × βᵒᵖ)ᵒᵖ)

instance  [Max α] [Max β] [IsLattice α] [IsLattice β] : IsLattice (α × β) := {
  inferInstanceAs (IsSemiLatticeMax (α × β)), inferInstanceAs (IsSemiLatticeMin (α × β)) with
}
