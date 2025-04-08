import Math.Order.Defs

variable {α: Type*}

instance : LE (α -> α -> Prop) where
  le a b := ∀{x y}, a x y -> b x y

instance : LT (α -> α -> Prop) where
  lt a b := a ≤ b ∧ ¬b ≤ a

instance : Max (α -> α -> Prop) where
  max a b x y := a x y ∨ b x y

instance : Min (α -> α -> Prop) where
  min a b x y := a x y ∧ b x y

instance : Top (α -> α -> Prop) where
  top _ _ := True
instance : Bot (α -> α -> Prop) where
  bot _ _ := False

instance : IsLattice (α -> α -> Prop) where
  lt_iff_le_and_not_le := Iff.rfl
  le_refl _ := id
  le_trans ab bc := bc ∘ ab
  le_antisymm ab ba := by
    ext x y; apply Iff.intro
    apply ab
    apply ba
  le_max_left _ _ := Or.inl
  le_max_right _ _ := Or.inr
  min_le_left _ _ := And.left
  min_le_right _ _ := And.right
  max_le ak bk := by
    intro x y h
    cases h
    apply ak; assumption
    apply bk; assumption
  le_min ak bk := by
    intro x y h
    exact ⟨ak h, bk h⟩

instance : IsLawfulTop (α -> α -> Prop) where
  le_top _ _ _ _ := True.intro

instance : IsLawfulBot (α -> α -> Prop) where
  bot_le _ _ _ := False.elim
