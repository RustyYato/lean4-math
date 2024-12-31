
instance : LE Cardinal.{u} where
  le := by
    apply Quotient.lift₂ (fun a b => Nonempty (a ↪ b))
    suffices ∀a b c d: Type u, a ≃ c -> b ≃ d -> (a ↪ b) -> c ↪ d by
      intro a b c d ⟨ac⟩ ⟨bd⟩
      apply propext
      apply Iff.intro
      intro ⟨h⟩
      apply Nonempty.intro
      apply this <;> assumption
      intro ⟨h⟩
      apply Nonempty.intro
      apply this
      symm; assumption
      symm; assumption
      assumption
    intro a b c d ac bd ab
    apply Embedding.congr
    assumption
    assumption
    assumption

@[simp]
def mk_le (a b: Type _) : (⟦a⟧ ≤ ⟦b⟧) = (Nonempty (a ↪ b)) := rfl

instance : LT Cardinal where
  lt a b := a ≤ b ∧ ¬b ≤ a

instance : IsLinearOrder Cardinal where
  lt_iff_le_and_not_le := Iff.rfl
  le_antisymm := by
    intro a b
    induction a, b using ind₂ with | mk a b =>
    intro ⟨ab⟩ ⟨ba⟩
    have ⟨eq, _⟩ := Equiv.ofBij (f := ab.toFun) (by
      apply And.intro
      exact ab.inj
      intro b'
      exists ba.toFun b'
      sorry)
    apply sound
    exact eq
  le_trans := by
    intro a b c
    induction a, b, c using ind₃ with | mk a b c =>
    intro ⟨ab⟩ ⟨bc⟩
    apply Nonempty.intro
    exact bc.comp ab
  lt_or_le := by
    intro a b
    by_cases h:b ≤ a
    right; assumption
    left
    induction a, b using ind₂ with | mk a b =>
    apply And.intro _ h
    replace h : (b ↪ a) -> False := by
      intro g
      apply h
      apply Nonempty.intro
      assumption
    apply Nonempty.intro
    sorry
