import Math.Data.Set.Order.Bounds
import Math.Order.Lattice.Basic


namespace Set

variable [LE α] [LT α] [IsPreOrder α] [Sup α] [IsSemiLatticeSup α] [Inf α] [IsSemiLatticeInf α]

def BoundedAbove.insert {a: α} {as: Set α} (h: BoundedAbove as) : BoundedAbove (insert a as) := by
  obtain ⟨x, h⟩ := h
  exists a ⊔ x
  intro x mem
  cases Set.mem_insert.mp mem
  subst x
  apply le_sup_left
  apply flip le_trans
  apply le_sup_right
  apply h
  assumption

def BoundedBelow.insert {a: α} {as: Set α} (h: BoundedBelow as) : BoundedBelow (insert a as) :=
  BoundedAbove.insert (α := OrderDual α) h

end Set
