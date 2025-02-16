import Math.Order.Lattice.Complete

variable {α: Type*}

instance : LE (α -> α -> Prop) where
  le a b := ∀{x y}, a x y -> b x y

instance : LT (α -> α -> Prop) where
  lt a b := a ≤ b ∧ ¬b ≤ a

instance : Sup (α -> α -> Prop) where
  sup a b x y := a x y ∨ b x y

instance : Inf (α -> α -> Prop) where
  inf a b x y := a x y ∧ b x y

instance : SupSet (α -> α -> Prop) where
  sSup S x y := ∃r ∈ S, r x y

instance : InfSet (α -> α -> Prop) where
  sInf S x y := ∀r ∈ S, r x y

instance : Top (α -> α -> Prop) where
  top _ _ := True
instance : Bot (α -> α -> Prop) where
  bot _ _ := False

instance : IsCompleteLattice (α -> α -> Prop) where
  lt_iff_le_and_not_le := Iff.rfl
  le_refl _ := id
  le_trans ab bc := bc ∘ ab
  le_antisymm ab ba := by
    ext x y; apply Iff.intro
    apply ab
    apply ba
  le_top _ _ _ _ := True.intro
  bot_le _ _ _ := False.elim
  le_sup_left _ _ := Or.inl
  le_sup_right _ _ := Or.inr
  inf_le_left _ _ := And.left
  inf_le_right _ _ := And.right
  sup_le ak bk := by
    intro x y h
    cases h
    apply ak; assumption
    apply bk; assumption
  le_inf ak bk := by
    intro x y h
    exact ⟨ak h, bk h⟩
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
