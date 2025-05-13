import Math.Order.Disjoint
import Math.Data.Set.Basic
import Math.Data.Set.Order.Basic

namespace Set

def not_disjoint_iff_nonempty_inter {a b: Set α} :
  ¬Disjoint a b ↔ (a ∩ b).Nonempty := by
  apply Iff.intro
  intro h
  simp [Disjoint] at h
  obtain ⟨t, tsuba, tsubb, tnonempty⟩ := h
  rcases t.empty_or_nonempty with rfl | ⟨x, hx⟩
  contradiction
  exists x
  apply And.intro
  apply tsuba; assumption
  apply tsubb; assumption
  intro ⟨x, ha, hb⟩ h
  have := h {x} ?_ ?_ x rfl
  contradiction
  apply (singleton_sub _ _).mpr
  assumption
  apply (singleton_sub _ _).mpr
  assumption
def subset_compl_iff_disjoint_right.{u} {α : Type u} {s t : Set α} : s ⊆ tᶜ ↔ Disjoint s t := by
  apply Iff.intro
  intro h u hs ht x hx
  have := h _ (hs _ hx) (ht _ hx)
  contradiction
  intro d x hs ht
  apply d {x}
  rintro _ rfl; assumption
  rintro _ rfl; assumption
  rfl

end Set
