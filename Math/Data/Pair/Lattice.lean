import Math.Data.Pair.Basic
import Math.Order.Lattice.Basic

variable [LE α] [LE β] [LT α] [LT β] [Sup α] [Sup β] [Inf α] [Inf β]

instance : Sup (α × β) where
  sup x y := (x.1 ⊔ y.1, x.2 ⊔ y.2)
instance : Inf (α × β) where
  inf x y := (x.1 ⊓ y.1, x.2 ⊓ y.2)

instance  [Sup α] [Sup β] [IsSemiLatticeSup α] [IsSemiLatticeSup β] : IsSemiLatticeSup (α × β) where
  le_sup_left _ _ := ⟨le_sup_left _ _, le_sup_left _ _⟩
  le_sup_right _ _ := ⟨le_sup_right _ _, le_sup_right _ _⟩
  sup_le ha hb := ⟨sup_le ha.left hb.left, sup_le ha.right hb.right⟩

instance  [Sup α] [Sup β] [IsSemiLatticeInf α] [IsSemiLatticeInf β] : IsSemiLatticeInf (α × β) :=
  inferInstanceAs (IsSemiLatticeInf (αᵒᵖ × βᵒᵖ)ᵒᵖ)

instance  [Sup α] [Sup β] [IsLattice α] [IsLattice β] : IsLattice (α × β) := {
  inferInstanceAs (IsSemiLatticeSup (α × β)), inferInstanceAs (IsSemiLatticeInf (α × β)) with
}
