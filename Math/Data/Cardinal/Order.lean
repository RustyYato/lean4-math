import Math.Data.Cardinal.Basic
import Math.Data.Ordinal.Basic
import Math.Data.Ordinal.WellOrdering
import Math.Type.Antisymm
import Math.Order.Lattice.Linear
import Math.Data.Set.Finite

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

private def exists_ord (c: Cardinal.{u}) : ∃o: Ordinal, o.card = c := by
  cases c with | mk α =>
  exists Ordinal.type (WellOrdering.order (α := α))

instance {α: Type*} : Nonempty { r: α -> α -> Prop // Relation.IsWellOrder r } := ⟨⟨WellOrdering.order α, inferInstance⟩⟩

instance : Nonempty (Set.preimage {c} Ordinal.card) := by
  cases c with | mk c =>
  exact ⟨Ordinal.type (WellOrdering.order c), rfl⟩

-- ord is the smallest ordinal that has cardinality as c
noncomputable
def ord (c: Cardinal): Ordinal := ⨅x: Set.preimage {c} Ordinal.card, x.val

def ord_eq (α: Type*) : ∃ (r : α → α → Prop) (_wo: Relation.IsWellOrder r), ord ⟦α⟧ = Ordinal.type r := by
  unfold ord
  have := ciInf_mem fun r : Set.preimage {⟦α⟧} Ordinal.card => r.val
  obtain ⟨⟨o, mem⟩, eq⟩ := this
  dsimp at eq
  replace mem : o.card = ⟦α⟧ := mem
  cases o with | mk o =>
  replace ⟨mem⟩ := Cardinal.exact mem
  let rel : α -> α -> Prop := fun x y => o.rel (mem.symm x) (mem.symm y)
  let eqv : o.rel ≃r rel := {
    toEquiv := mem
    resp_rel := by
      intro x y
      show o.rel x y ↔ o.rel (mem.symm (mem _)) (mem.symm (mem _))
      rw [mem.coe_symm, mem.coe_symm]
  }

  refine ⟨?_, ?_, ?_⟩
  exact rel
  exact eqv.symm.toRelEmbedding.wo
  rw [eq]
  apply Ordinal.sound
  assumption

def ord_card (c: Cardinal) : c.ord.card = c := by
  cases c with | mk α =>
  have ⟨r, wo, eq⟩ := ord_eq α
  rw [eq]
  rfl

def ord_inj : Function.Injective ord := by
  intro a b eq
  rw [←ord_card a, ←ord_card b, eq]

def ord_is_min (c: Cardinal) : ∀o < c.ord, o.card ≠ c := by
  intro o o_lt_ord
  cases c with | mk c =>
  cases o with | mk o =>
  show ⟦o.ty⟧ ≠ ⟦c⟧
  replace o_lt_ord : Ordinal.mk o < iInf _ := o_lt_ord
  have := not_mem_of_lt_csInf o_lt_ord (Set.allBoundedBelow _)
  rw [Set.mem_range] at this
  intro g
  replace ⟨g⟩ := Quotient.exact g
  apply this
  let rel : c -> c -> Prop := fun x y => o.rel (g.symm x) (g.symm y)
  have : o.rel ≃r rel := {
    toEquiv := g
    resp_rel := by
      intro x y
      show o.rel x y ↔ o.rel (g.symm (g x)) (g.symm (g y))
      rw [g.coe_symm, g.coe_symm]
  }
  refine ⟨⟨?_, ?_⟩, ?_⟩
  exact Ordinal.mk o
  apply sound
  assumption
  rfl

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

noncomputable def oemb_ord : Cardinal ↪o Ordinal where
  toFun := ord
  inj' _ _ h := ord_inj h
  map_le := by
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
    apply lt_of_not_le
    intro g'
    apply g; clear g
    have ⟨ar, awo, eqa⟩ := ord_eq a
    have ⟨br, bwo, eqb⟩ := ord_eq b
    rw [eqa, eqb] at g'
    obtain ⟨g'⟩ := g'
    exact ⟨g'.toEmbedding⟩

noncomputable def remb_ord_lt : @RelEmbedding Cardinal Ordinal (· < ·) (· < ·) :=
  oemb_ord.toLtRelEmbedding

instance : IsLinearOrder Cardinal := oemb_ord.instIsLinearOrder

instance : @Relation.IsWellOrder Cardinal (· < ·) := remb_ord_lt.wo

noncomputable def initseg_ord : @InitialSegment Cardinal Ordinal (· < ·) (· < ·) :=
  Classical.choice (InitialSegment.collapse ⟨remb_ord_lt⟩)

open Classical

def natCast_lt_ℵ₀ (n: ℕ) : n < ℵ₀ where
  left := by
    refine ⟨?_⟩
    apply Equiv.congrEmbed (Equiv.ulift _).symm .rfl _
    apply Equiv.congrEmbed Equiv.fin_equiv_nat_subtype.symm .rfl _
    apply Embedding.subtypeVal
  right := by
    intro ⟨h⟩
    replace h := Equiv.congrEmbed .rfl (Equiv.ulift _) h
    have := Equiv.antisymm h (Equiv.congrEmbed Equiv.fin_equiv_nat_subtype.symm .rfl Embedding.subtypeVal)
    have : Fintype ℕ := Fintype.ofEquiv this
    exact Fintype.nat_not_fintype this

private noncomputable def findDifferent
  (emb: Fin (n + 1) ↪ α)
  (f: Fin n -> α) (x: Nat) (h: x ≤ n)
  (g: ∀x, emb x ∈ Set.range f): α :=
  match x with
  | 0 => by
    exfalso
    have := Fintype.ofIsFinite (Set.range f)
    have := Fintype.ofIsFinite (Set.range emb)
    have : Fintype.card (Set.range f) ≤ n := by
      conv => { rhs; rw [←Fintype.card_fin n] }
      apply Fintype.card_le_of_embed
      refine ⟨?_, ?_⟩
      intro ⟨x, hx⟩
      exact Classical.choose hx
      intro ⟨x, hx⟩ ⟨y, hy⟩ eq
      dsimp at eq
      congr
      rw [Classical.choose_spec hx, Classical.choose_spec hy, eq]
    have : Fintype.card (Set.range emb) ≤ Fintype.card (Set.range f) := by
      apply Fintype.card_le_of_embed
      refine ⟨?_, ?_⟩
      intro ⟨x, hx⟩
      refine ⟨?_, ?_⟩
      assumption
      obtain ⟨i, eq⟩ := hx
      have := g i
      rw [←eq] at this
      assumption
      intro x y eq
      dsimp at eq
      cases x; cases y;cases eq
      rfl
    -- have := Fintype.card_embed

    sorry
  | x + 1 =>
    let a := emb ⟨x, by
      apply Nat.lt_of_succ_le
      apply Nat.le_trans h
      apply Nat.le_succ⟩
    if a  ∈ Set.range f then
      findDifferent emb f x sorry sorry
    else
      a

private noncomputable def toInfinite (embs: ∀n: ℕ, n ≤ #α) (n: ℕ) : α :=
  have : ∃a: α, ∀x (h: x < n), toInfinite embs x ≠ a := by
    have emb := Classical.choice (embs (n + 1))
    replace emb := Equiv.congrEmbed (Equiv.ulift _) .rfl emb
    let finv : Fin n -> α := fun x => toInfinite embs x.val

    sorry

  sorry
termination_by n
decreasing_by
  any_goals assumption
  apply Fin.isLt


def aleph0_le {c : Cardinal} : ℵ₀ ≤ c ↔ ∀ n : ℕ, ↑n ≤ c := by
  cases c with | mk α =>
  apply Iff.intro
  intro ⟨h⟩ n
  have := h
  refine ⟨?_⟩
  apply Embedding.trans _ this
  apply Equiv.congrEmbed (Equiv.ulift _).symm .rfl _
  apply Equiv.congrEmbed Equiv.fin_equiv_nat_subtype.symm .rfl _
  apply Embedding.subtypeVal
  intro h
  refine ⟨?_⟩
  refine ⟨?_, ?_⟩
  intro n
  sorry
  sorry

def lt_ℵ₀ (c: Cardinal) : c < ℵ₀ ↔ ∃n: Nat, c = n := by
  apply flip Iff.intro
  rintro ⟨n, rfl⟩
  apply natCast_lt_ℵ₀
  cases c with | mk α =>
  intro ⟨⟨h⟩, g⟩
  replace g := g ∘ Nonempty.intro
  apply Classical.byContradiction
  intro notfin
  rw [not_exists] at notfin
  apply g
  refine ⟨?_, ?_⟩
  · have := fun n => (notfin n) ∘ Quotient.sound ∘ Nonempty.intro
    intro n
    sorry
  · sorry

end Cardinal
