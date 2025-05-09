import Math.Data.Ordinal.Defs
import Math.Data.Cardinal.PartialOrder
import Math.Data.Ordinal.WellOrdering

namespace Ordinal

def toCardinal : Ordinal -> Cardinal := by
  refine Ordinal.lift (fun α _ _ => #α) ?_
  intro α β _ _ _ _ eq
  apply Cardinal.sound
  exact eq.toEquiv

-- a monotone homomorphism from the ordinals to the cardinals
-- this doesn't map relations backwards since `ω+1` and `ω`
-- have the same cardinality, so if it mapped relations backwards
-- it would allow proving that `ω+1 ≤ ω`
def card : Ordinal →≤ Cardinal where
  toFun := toCardinal
  monotone a b := by
    cases a with | _ A rela =>
    cases b with | _ B relb =>
    intro ⟨h⟩
    exact ⟨h.toEmbedding⟩

end Ordinal

namespace Cardinal

private def exists_ord (c: Cardinal.{u}) : ∃o: Ordinal, o.card = c := by
  cases c with | mk α =>
  exists Ordinal.type (WellOrdering.order (α := α))

instance {α: Type*} : Nonempty { r: α -> α -> Prop // Relation.IsWellOrder r } := ⟨⟨WellOrdering.order α, inferInstance⟩⟩

instance : Nonempty (Set.preimage {c} Ordinal.card) := by
  cases c with | mk c =>
  exact ⟨Ordinal.type (WellOrdering.order c), rfl⟩

-- ord is the smallest ordinal that has cardinality as c
private noncomputable def toOrdinal (c: Cardinal): Ordinal := ⨅x: Set.preimage {c} Ordinal.card, x.val

private def toOrdinal_eq (α: Type*) : ∃ (r : α → α → Prop) (_wo: Relation.IsWellOrder r), toOrdinal ⟦α⟧ = Ordinal.type r := by
  unfold toOrdinal
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

private def toOrdinal_card (c: Cardinal) : c.toOrdinal.card = c := by
  cases c with | mk α =>
  have ⟨r, wo, eq⟩ := toOrdinal_eq α
  rw [eq]
  rfl

private def toOrdinal_inj : Function.Injective toOrdinal := by
  intro a b eq
  rw [←toOrdinal_card a, ←toOrdinal_card b, eq]

private def toOrdinal_is_min' (c: Cardinal) : ∀o < c.toOrdinal, o.card ≠ c := by
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

private def toOrdinal_is_min (c: Cardinal) : ∀o < c.toOrdinal, o.card < c := by
  intro o h
  have := toOrdinal_is_min' _ _ h
  rw [←toOrdinal_card c]
  suffices o.card ≤ c.toOrdinal.card by
    apply lt_of_le_of_ne
    assumption
    rw [toOrdinal_card]
    assumption
  generalize hc':c.toOrdinal = c'
  cases o with | _ A rela =>
  cases c' with | _ _ c' =>
  rw [hc'] at h
  obtain ⟨h⟩ := h
  refine ⟨?_⟩
  exact h.toEmbedding

-- a function which sends each cardinal to the first
-- ordinal with the given cardinality
noncomputable def ord : Cardinal ↪o Ordinal where
  toFun := toOrdinal
  inj' _ _ h := toOrdinal_inj h
  map_le := by
    intro a b
    suffices a < b -> a.toOrdinal < b.toOrdinal by
      apply Iff.intro
      · intro h
        cases lt_or_eq_of_le h <;> rename_i h
        apply le_of_lt
        apply this
        assumption
        rw [h]
      · intro h
        cases lt_or_eq_of_le h <;> rename_i h
        have := toOrdinal_is_min _ _ h
        rw [toOrdinal_card] at this
        apply le_of_lt
        assumption
        rw [toOrdinal_inj h]
    induction a, b using ind₂ with | mk a b =>
    intro ⟨⟨h⟩, g⟩
    apply lt_of_not_le
    intro g'
    apply g; clear g
    have ⟨ar, awo, eqa⟩ := toOrdinal_eq a
    have ⟨br, bwo, eqb⟩ := toOrdinal_eq b
    rw [eqa, eqb] at g'
    obtain ⟨g'⟩ := g'
    exact ⟨g'.toEmbedding⟩

def ord_is_min (c: Cardinal) : ∀o < c.ord, o.card < c := toOrdinal_is_min c

noncomputable def remb_ord_lt : @RelEmbedding Cardinal Ordinal (· < ·) (· < ·) :=
  ord.toLtRelEmbedding

noncomputable def initseg_ord : @InitialSegment Cardinal Ordinal (· < ·) (· < ·) :=
  Classical.choice (InitialSegment.collapse ⟨remb_ord_lt⟩)

def ord_card (c: Cardinal) : c.ord.card = c := by
  apply toOrdinal_card

instance : @Relation.IsWellOrder Cardinal (· < ·) := remb_ord_lt.lift_wo

def initseg_ord_le_ord (c: Cardinal) : initseg_ord c ≤ ord c := by
  rw [←not_lt]
  intro h
  induction c using Relation.wfInduction (· < ·: Relation Cardinal) with
  | h c ih =>
  have ⟨x, hx⟩ := initseg_ord.isInitial _ _ h
  simp at hx
  have x_lt_c := h
  rw [hx] at x_lt_c
  replace x_lt_c := initseg_ord.resp_rel.mpr x_lt_c
  apply ih x x_lt_c
  rw [←hx]
  rw [←not_le]
  intro h; have := (Cardinal.ord.map_le _ _).mpr h
  rw [←not_lt] at this
  contradiction

end Cardinal

namespace Ordinal

def card_ord (o: Ordinal) : o.card.ord ≤ o := by
  rw [←not_lt]; intro h
  exact lt_irrefl (Cardinal.ord_is_min o.card _ h)

namespace Omega

def IsInitial (o: Ordinal) : Prop := o.card.ord = o

noncomputable def initEquivCard : Subtype IsInitial ≃o Cardinal where
  toFun x := x.val.card
  invFun x := ⟨x.ord, by
    unfold IsInitial
    rw [Cardinal.ord_card]⟩
  leftInv x := by simp; congr; rw [x.property]
  rightInv x := by
    simp
    rw [Cardinal.ord_card]
  map_le := by
    intro a b
    apply Iff.intro
    apply card.monotone
    intro h
    show a.val ≤ b.val
    rw [←a.property, ←b.property]
    apply (Cardinal.ord.map_le _ _).mp
    assumption

def type_init_eq_type_card : type (Relation.subtype_rel (· < ·) IsInitial) = type (· < ·: Relation Cardinal) := by
  apply sound
  exact {
    initEquivCard with
    resp_rel := by
      intro x y
      simp
      show x.val < y.val ↔ _
      erw [←not_le, ←not_le, ←initEquivCard.map_le]
      rfl
  }

end Omega

end Ordinal
