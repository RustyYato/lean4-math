import Math.Data.Cardinal.Basic
import Math.Data.Ordinal.Basic
import Math.Data.Ordinal.WellOrdering
import Math.Type.Antisymm

namespace Ordinal

def card (o: Ordinal) : Cardinal := by
  apply Quotient.liftOn o _ _
  intro x
  exact Cardinal.mk x.ty
  intro a b ⟨eq⟩
  apply Cardinal.sound
  exact eq.toEquiv

end Ordinal

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
    apply Embedding.congr
    assumption
    assumption
    assumption

@[simp]
def mk_le (a b: Type _) : (⟦a⟧ ≤ ⟦b⟧) = (Nonempty (a ↪ b)) := rfl

instance : LT Cardinal where
  lt a b := a ≤ b ∧ ¬b ≤ a

instance : IsPartialOrder Cardinal where
  lt_iff_le_and_not_le := Iff.rfl
  le_refl a := by
    induction a with | mk a =>
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

private def exists_ord (c: Cardinal.{u}) : ∃o: Ordinal, o.card = c := by
  induction c with | mk α =>
  exists Ordinal.type (WellOrdering.order (α := α))

noncomputable
def ord (c: Cardinal) := Ordinal.min_of (exists_ord c)

def ord_inj {a b: Cardinal} : a.ord = b.ord -> a = b := by
  intro eq
  have ha : a.ord.card = a := Ordinal.min_of_spec (exists_ord a)
  have hb : b.ord.card = b := Ordinal.min_of_spec (exists_ord b)
  rw [eq] at ha
  rw [←ha, hb]

def ord_card (c: Cardinal) : c.ord.card = c :=
  Ordinal.min_of_spec (exists_ord c)

def ord_is_min (c: Cardinal) : ∀o < c.ord, o.card ≠ c :=
  Ordinal.min_of_is_min (exists_ord c)

def ord_is_min' (c: Cardinal) : ∀o < c.ord, o.card < c := by
  intro o h
  have := ord_is_min _ _ h
  rw [←ord_card c]
  suffices o.card ≤ c.ord.card by
    apply lt_of_le_of_ne
    assumption
    rw [ord_card]
    assumption
  generalize hc':c.ord = c'
  cases o with | mk o =>
  cases c' with | mk c' =>
  rw [hc'] at h
  obtain ⟨h⟩ := h
  refine ⟨?_⟩
  exact h.toEmbedding

noncomputable def oemb_ord : OrderEmbedding Cardinal Ordinal where
  toFun := ord
  inj _ _ h := ord_inj h
  resp_rel := by
    intro a b; dsimp
    suffices a < b -> a.ord < b.ord by
      apply Iff.intro
      · intro h
        cases lt_or_eq_of_le h <;> rename_i h
        apply le_of_lt
        apply this
        assumption
        rw [h]
      · intro h
        cases lt_or_eq_of_le h <;> rename_i h
        have := ord_is_min' _ _ h
        rw [ord_card] at this
        apply le_of_lt
        assumption
        rw [ord_inj h]
    induction a, b using ind₂ with | mk a b =>
    intro ⟨⟨h⟩, g⟩


    sorry

instance : IsLinearOrder Cardinal where
  lt_iff_le_and_not_le := Iff.rfl
  le_antisymm := le_antisymm
  le_trans := le_trans
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

end Cardinal
