import Math.Order.Lattice.Complete
import Math.Relation.Order

variable {α: Type*}

instance : SupSet (α -> α -> Prop) where
  sSup S x y := ∃r ∈ S, r x y

instance : InfSet (α -> α -> Prop) where
  sInf S x y := ∀r ∈ S, r x y

instance : IsCompleteLattice (α -> α -> Prop) where
  le_sSup := by
    intro S r h _ _ _
    exists r
  sSup_le := by
    intro r S h x y ⟨r₀, _, _⟩
    apply h
    assumption
    assumption
  le_sInf := by
    intro r S  h x y g _ _
    apply h
    assumption
    assumption
  sInf_le := by
    intro S r _ _ _ h
    apply h
    assumption
