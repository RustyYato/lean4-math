import Math.Order.Defs
import Math.Order.TopBot

variable (α: Type*) [LE α] [LT α]
variable {α₀: Type*} [Max α₀] [Min α₀] [LE α₀] [LT α₀]

class SemiLatticeMax extends LawfulSup α, IsPartialOrder α where
  max_le: ∀{a b k: α}, a ≤ k -> b ≤ k -> a ⊔ b ≤ k

class SemiLatticeMin extends LawfulInf α, IsPartialOrder α where
  le_min: ∀{a b k: α}, k ≤ a -> k ≤ b -> k ≤ a ⊓ b

class Lattice extends SemiLatticeMax α, SemiLatticeMin α where
  mk' ::

instance [Max α] [IsSemiLatticeMax α] : IsSemiLatticeMin αᵒᵖ where
  le_min := max_le (α := α)

instance [Min α] [IsSemiLatticeMin α] : IsSemiLatticeMax αᵒᵖ where
  max_le := le_min (α := α)

instance [Max α] [Min α] [IsLattice α] : IsLattice αᵒᵖ where
  toIsSemiLatticeMax := inferInstance
  min_le_left := min_le_left
  min_le_right := min_le_right
  le_min := le_min

instance [h: SemiLatticeMax α] : IsSemiLatticeMax α where
  max_le := h.max_le

instance [h: SemiLatticeMin α] : IsSemiLatticeMin α where
  le_min := h.le_min

instance [SemiLatticeMax α] : SemiLatticeMin αᵒᵖ where
  le_min := max_le (α := α)

instance [SemiLatticeMin α] : SemiLatticeMax αᵒᵖ where
  max_le := le_min (α := α)

instance [Lattice α] : IsLattice α where
  le_min := le_min

instance [Lattice α] : Lattice αᵒᵖ where
  le_min := le_min

instance [h: SemiLatticeMax α] [g: SemiLatticeMin α] : Lattice α where
  le_min := g.le_min

attribute [simp] le_max_left le_max_right
attribute [simp] min_le_left min_le_right

variable (α: Type*) [Max α] [Min α] [LE α] [LT α]

class IsDistribLattice extends IsLattice α where
  le_max_min : ∀{x y z : α}, (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ y ⊓ z

section

variable [IsDistribLattice α₀]

theorem le_max_min : ∀ {x y z : α₀}, (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ y ⊓ z :=
  IsDistribLattice.le_max_min

end

def SemiLatticeMax.opposite (c: SemiLatticeMax α) : SemiLatticeMin αᵒᵖ := inferInstance
def SemiLatticeMin.opposite (c: SemiLatticeMin α) : SemiLatticeMax αᵒᵖ := inferInstance
def Lattice.opposite (c: Lattice α) : Lattice αᵒᵖ := inferInstance
