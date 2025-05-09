import Math.Data.Ordinal.Card
import Math.Order.GaloisConnection

namespace Cardinal

instance : IsLinearOrder Cardinal := ord.instIsLinearOrder

noncomputable def gciOrdinal : GaloisCoinsertion ord Ordinal.card where
  gc := by
    intro c o
    apply Iff.intro
    intro h
    rw [← ord_card c]
    apply Ordinal.card.monotone
    assumption
    intro h
    apply flip le_trans
    apply Ordinal.card_ord
    apply (ord.map_le _ _).mp
    assumption
  u_l_le o := by rw [ord_card]
  choice x hx := x.card
  choice_eq := by
    intro o ho
    rfl
noncomputable def giOrdinal := gciOrdinal.dual

private noncomputable def lattice := giOrdinal.liftConditionallyCompleteLattice

private noncomputable instance : ConditionallyCompleteLatticeOps Cardinalᵒᵖ := lattice.fst
noncomputable instance ops : ConditionallyCompleteLatticeOps Cardinal := inferInstanceAs (ConditionallyCompleteLatticeOps (Cardinal ᵒᵖ ᵒᵖ))

private noncomputable instance : IsConditionallyCompleteLattice Cardinalᵒᵖ := lattice.snd
noncomputable instance : IsConditionallyCompleteLattice Cardinal := inferInstanceAs (IsConditionallyCompleteLattice (Cardinal ᵒᵖ ᵒᵖ))

instance : Bot Cardinal := ⟨0⟩

instance : IsLawfulBot Cardinal where
  bot_le c := by
    induction c using ind with
    | _ c =>
    exact ⟨Embedding.empty⟩

protected def BoundedBelow (S: Set Cardinal) : S.BoundedBelow := ⟨⊥, by
  intro x hx
  apply bot_le⟩

end Cardinal
