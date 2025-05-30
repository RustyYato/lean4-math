import Math.Data.Fintype.Impls.LazyFinset
import Math.Order.Defs

namespace LazyFinset

instance : LE (LazyFinset α) where
  le a b := a ⊆ b
instance : LT (LazyFinset α) where
  lt a b := a ≤ b ∧ ¬b ≤ a
instance : Max (LazyFinset α) where
  max a b := a ++ b

instance : IsSemiLatticeMax (LazyFinset α) where
  le_refl _ _ := id
  le_trans f g _ h := g _ (f _ h)
  le_antisymm h₀ h₁ := by
    ext; apply Iff.intro
    apply h₀
    apply h₁
  le_max_left := by
    intro a b x ha
    show x ∈ a ++ b
    simp [ha]
  le_max_right := by
    intro a b x hb
    show x ∈ a ++ b
    simp [hb]
  max_le := by
    intro a b k ak bk
    show a ++ b ⊆ k
    intro x hx
    simp at hx
    cases hx
    apply ak; assumption
    apply bk; assumption

end LazyFinset
