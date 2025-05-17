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

private instance : IsConditionallyCompleteLattice Cardinalᵒᵖ := lattice.snd
instance : IsConditionallyCompleteLattice Cardinal := inferInstanceAs (IsConditionallyCompleteLattice (Cardinal ᵒᵖ ᵒᵖ))

instance : IsLinearLattice Cardinal where

instance : Bot Cardinal := ⟨0⟩

instance : IsLawfulBot Cardinal where
  bot_le c := by
    induction c using ind with
    | _ c =>
    exact ⟨Embedding.empty⟩

protected def BoundedBelow (S: Set Cardinal) : S.BoundedBelow := ⟨⊥, by
  intro x hx
  apply bot_le⟩

def card_range_emb (f: α ↪ β) : #(Set.range f) = #α := by
  have (x: Set.range f) : ∃a, x = f a := by exact x.property
  replace := Classical.axiomOfChoice this
  obtain ⟨g, hg⟩ := this
  apply sound
  exact {
    toFun := g
    invFun x := ⟨f x, Set.mem_range'⟩
    leftInv := by
      intro x
      simp
      congr; rw [←hg]
    rightInv := by
      intro x
      simp
      apply f.inj
      rw [←hg ⟨_, _⟩]
  }

def le_sum (f: ι -> Cardinal) (i: ι) : f i ≤ sum f := by
  rw [←type_spec (f i)]
  refine ⟨?_⟩
  exact {
    toFun x := ⟨i, x⟩
    inj' := by
      intro x y h; cases h
      rfl
  }

def _root_.IsNontrivial.of_card (α: Type*) (h: 2 ≤ #α) : IsNontrivial α := by
  obtain ⟨h⟩ := h
  exists h ⟨0⟩
  exists h ⟨1⟩
  intro g
  nomatch h.inj g

def lt_pow_self (a b: Cardinal) (h: 2 ≤ a) : b < a ^ b := by
  rw [←not_le]
  intro g
  cases a with | mk α =>
  cases b with | mk β =>
  have : IsNontrivial α := IsNontrivial.of_card _ h
  obtain ⟨g⟩ := g
  exact Embedding.cantor _ _ g

def ulift_lt_card_cardinal (c: Cardinal.{u}) : ulift.{u, u + 1} c < #Cardinal.{u} := by
  cases c
  rw [←not_le]
  intro ⟨h⟩
  replace h := Equiv.congrEmbed .rfl (Equiv.ulift _) h
  let g := Function.invFun h
  have left_inv := Function.leftinverse_of_invFun h.inj
  have invFun_surj := left_inv.Surjective
  have ⟨a, (ha : _ = g a)⟩ := invFun_surj (2 ^ sum g)
  have := le_sum g a
  rw [←ha] at this
  rw [←not_lt] at this
  apply this
  clear this ha a
  apply lt_pow_self
  rfl

end Cardinal
