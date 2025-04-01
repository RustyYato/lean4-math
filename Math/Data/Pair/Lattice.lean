import Math.Data.Pair.Basic
import Math.Order.Lattice.Basic

variable [LE α] [LE β] [LT α] [LT β] [Max α] [Max β] [Min α] [Min β]

instance : Max (α × β) where
  max x y := (x.1 ⊔ y.1, x.2 ⊔ y.2)
instance : Min (α × β) where
  min x y := (x.1 ⊓ y.1, x.2 ⊓ y.2)

instance  [Max α] [Max β] [IsSemiLatticeSup α] [IsSemiLatticeSup β] : IsSemiLatticeSup (α × β) where
  le_sup_left _ _ := ⟨le_sup_left _ _, le_sup_left _ _⟩
  le_sup_right _ _ := ⟨le_sup_right _ _, le_sup_right _ _⟩
  sup_le ha hb := ⟨sup_le ha.left hb.left, sup_le ha.right hb.right⟩

instance  [Max α] [Max β] [IsSemiLatticeInf α] [IsSemiLatticeInf β] : IsSemiLatticeInf (α × β) :=
  inferInstanceAs (IsSemiLatticeInf (αᵒᵖ × βᵒᵖ)ᵒᵖ)

instance  [Max α] [Max β] [IsLattice α] [IsLattice β] : IsLattice (α × β) := {
  inferInstanceAs (IsSemiLatticeSup (α × β)), inferInstanceAs (IsSemiLatticeInf (α × β)) with
}
