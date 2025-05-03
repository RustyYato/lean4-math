import Math.Data.Cardinal.Defs
import Math.Data.Ordinal.Defs
import Math.Data.Ordinal.WellOrdering
import Math.Type.Antisymm

namespace Ordinal

def card : Ordinal -> Cardinal := by
  refine Ordinal.lift (fun α _ _ => #α) ?_
  intro α β _ _ _ _ eq
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
  cases o with | _ A rela =>
  replace ⟨mem⟩ := Cardinal.exact mem
  let rel : α -> α -> Prop := fun x y => rela (mem.symm x) (mem.symm y)
  let eqv : rela ≃r rel := {
    toEquiv := mem
    resp_rel := by
      intro x y
      show rela x y ↔ rela (mem.symm (mem _)) (mem.symm (mem _))
      rw [mem.coe_symm, mem.coe_symm]
  }

  refine ⟨?_, ?_, ?_⟩
  exact rel
  exact eqv.symm.toRelEmbedding.lift_wo
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
  replace o_lt_ord : o < iInf _ := o_lt_ord
  cases o with | _ A rela =>
  show ⟦A⟧ ≠ ⟦c⟧
  have := not_mem_of_lt_csInf o_lt_ord (Set.allBoundedBelow _)
  rw [Set.mem_range] at this
  intro g
  replace ⟨g⟩ := Quotient.exact g
  apply this
  let rel : c -> c -> Prop := fun x y => rela (g.symm x) (g.symm y)
  have : rela ≃r rel := {
    toEquiv := g
    resp_rel := by
      intro x y
      simp [rel]
  }
  refine ⟨⟨?_, ?_⟩, ?_⟩
  exact Ordinal.type rela
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
  cases o with | _ A rela =>
  cases c' with | _ _ c' =>
  rw [hc'] at h
  obtain ⟨h⟩ := h
  refine ⟨?_⟩
  exact h.toEmbedding

noncomputable def oemb_ord : Cardinal ↪o Ordinal where
  toFun := ord
  inj' _ _ h := ord_inj h
  map_le := by
    intro a b
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

instance : @Relation.IsWellOrder Cardinal (· < ·) := remb_ord_lt.lift_wo

noncomputable def initseg_ord : @InitialSegment Cardinal Ordinal (· < ·) (· < ·) :=
  Classical.choice (InitialSegment.collapse ⟨remb_ord_lt⟩)

end Cardinal
