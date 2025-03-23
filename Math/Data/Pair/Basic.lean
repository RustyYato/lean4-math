import Math.Order.Defs

variable [LE α] [LE β] [LT α] [LT β]

instance : LE (α × β) where
  le x y := x.1 ≤ y.1 ∧ x.2 ≤ y.2

instance : LT (α × β) where
  lt x y := x ≤ y ∧ ¬y ≤ x

instance [IsLawfulLT α] [IsLawfulLT β] : IsLawfulLT (α × β) where
  lt_iff_le_and_not_le := Iff.rfl

instance [IsPreOrder α] [IsPreOrder β] : IsPreOrder (α × β) where
  le_refl _ := ⟨le_refl _, le_refl _⟩
  le_trans | ⟨a, b⟩, ⟨c, d⟩  => ⟨le_trans a c, le_trans b d⟩

instance [IsPartialOrder α] [IsPartialOrder β] : IsPartialOrder (α × β) where
  le_antisymm a b := by
    ext
    apply le_antisymm
    exact a.left
    exact b.left
    apply le_antisymm
    exact a.right
    exact b.right
