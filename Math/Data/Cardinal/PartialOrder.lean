import Math.Data.Cardinal.Defs
import Math.Type.Antisymm
import Math.Order.Defs

namespace Cardinal

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
    apply Equiv.congrEmbed _ _ ab
    assumption
    assumption

@[simp]
def mk_le (a b: Type _) : (⟦a⟧ ≤ ⟦b⟧) = (Nonempty (a ↪ b)) := rfl

instance : LT Cardinal where
  lt a b := a ≤ b ∧ ¬b ≤ a

instance : IsPartialOrder Cardinal where
  lt_iff_le_and_not_le := Iff.rfl
  le_refl a := by
    cases a with | mk a =>
    refine ⟨?_⟩
    apply Embedding.refl
  le_antisymm := by
    intro a b
    induction a, b using ind₂ with | mk a b =>
    intro ⟨ab⟩ ⟨ba⟩
    apply sound
    exact Equiv.antisymm ab ba
  le_trans := by
    intro a b c
    induction a, b, c using ind₃ with | mk a b c =>
    intro ⟨ab⟩ ⟨bc⟩
    apply Nonempty.intro
    exact bc.comp ab

end Cardinal
