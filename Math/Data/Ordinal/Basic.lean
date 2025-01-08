import Math.Relation.Basic
import Math.Relation.RelIso
import Math.Tactics.PPWithUniv
import Math.Relation.Segments
import Math.Order.Linear
import Math.AxiomBlame

namespace Ordinal

@[pp_with_univ]
structure Pre.{u} where
  ty: Type u
  rel: ty -> ty -> Prop
  wo: Relation.IsWellOrder rel := by infer_instance

instance (p: Pre) : Relation.IsWellOrder p.rel := p.wo

instance pre_setoid : Setoid Pre where
  r a b := Nonempty (a.rel ≃r b.rel)
  iseqv := {
    refl _ := ⟨RelIso.refl⟩
    symm | ⟨h⟩ => ⟨h.symm⟩
    trans | ⟨h⟩, ⟨g⟩ => ⟨h.trans g⟩
  }

@[pp_with_univ]
def _root_.Ordinal := Quotient pre_setoid
def mk : Pre -> Ordinal := Quotient.mk _
local notation "⟦" x "⟧" => Ordinal.mk x
def ind : {motive: Ordinal -> Prop} -> (mk: ∀a, motive ⟦a⟧) -> ∀a, motive a := Quotient.ind
def ind₂ : {motive: Ordinal -> Ordinal -> Prop} -> (mk: ∀a b, motive ⟦a⟧ ⟦b⟧) -> ∀a b, motive a b := Quotient.ind₂
def ind₃ : {motive: Ordinal -> Ordinal -> Ordinal -> Prop} -> (mk: ∀a b c, motive ⟦a⟧ ⟦b⟧ ⟦c⟧) -> ∀a b c, motive a b c := by
  intro motive h a b c
  induction a, b using ind₂ with | mk a b =>
  induction c using ind with | mk c =>
  apply h
def ind₄ : {motive: Ordinal -> Ordinal -> Ordinal -> Ordinal -> Prop} -> (mk: ∀a b c d, motive ⟦a⟧ ⟦b⟧ ⟦c⟧ ⟦d⟧) -> ∀a b c d, motive a b c d := by
  intro motive h a b c d
  induction a, b using ind₂ with | mk a b =>
  induction c, d using ind₂ with | mk c d =>
  apply h
def sound {a b: Pre} : a.rel ≃r b.rel -> ⟦a⟧ = ⟦b⟧ := Quotient.sound ∘ Nonempty.intro

def type (rel: α -> α -> Prop) [Relation.IsWellOrder rel] := ⟦.mk _ rel⟧

def Pre.lift (a: Pre.{u}): Pre.{max u v} where
  ty := ULift a.ty
  rel x y := a.rel x.down y.down
  wo := (ULift.relIso _).toRelEmbedding.wo

def lift : Ordinal -> Ordinal := by
  apply Quotient.lift (fun _ => ⟦_⟧) _
  exact Pre.lift
  intro a b ⟨eq⟩
  apply sound
  apply RelIso.trans (ULift.relIso _)
  apply RelIso.trans _ (ULift.relIso _).symm
  assumption

instance : LE Ordinal.{u} where
  le := by
    refine Quotient.lift₂ ?_ ?_
    intro ⟨a, ar, arwo⟩ ⟨b, br, brwo⟩
    exact Nonempty (ar ≼i br)
    suffices ∀a b c d: Pre.{u}, a.rel ≃r c.rel -> b.rel ≃r d.rel -> a.rel ≼i b.rel -> c.rel ≼i d.rel by
      intro a b c d ⟨ac⟩ ⟨bd⟩
      dsimp
      apply propext
      apply Iff.intro
      intro ⟨ab⟩
      apply Nonempty.intro
      apply this <;> assumption
      intro ⟨ab⟩
      apply Nonempty.intro
      apply this _ _ _ _ _ _ ab <;> (symm; assumption)
    intro a b c d ac bd ab
    apply InitialSegment.congr <;> assumption

instance : LT Ordinal.{u} where
  lt := by
    refine Quotient.lift₂ ?_ ?_
    intro ⟨a, ar, arwo⟩ ⟨b, br, brwo⟩
    exact Nonempty (ar ≺i br)
    suffices ∀a b c d: Pre.{u}, a.rel ≃r c.rel -> b.rel ≃r d.rel -> a.rel ≺i b.rel -> c.rel ≺i d.rel by
      intro a b c d ⟨ac⟩ ⟨bd⟩
      dsimp
      apply propext
      apply Iff.intro
      intro ⟨ab⟩
      apply Nonempty.intro
      apply this <;> assumption
      intro ⟨ab⟩
      apply Nonempty.intro
      apply this _ _ _ _ _ _ ab <;> (symm; assumption)
    intro a b c d ac bd ab
    apply PrincipalSegment.congr <;> assumption

instance : IsPartialOrder Ordinal where
  lt_iff_le_and_not_le := by
    intro a b
    induction a, b using ind₂ with | mk a b =>
    show Nonempty _ ↔ Nonempty _ ∧ ¬Nonempty _
    apply Iff.intro
    intro ⟨h⟩
    apply And.intro ⟨h⟩
    intro ⟨g⟩
    have := InitialSegment.antisymm h g
    exact elim_empty <| h.congr this (RelIso.refl (rel := b.rel))
    intro ⟨⟨h⟩, g⟩
    rcases h.eqv_or_principal with surj | has_top
    have ⟨eqv, eq⟩  := Equiv.ofBij ⟨h.inj, surj⟩
    replace eq : eqv.toFun = h.toFun := eq
    have : a.rel ≃r b.rel := by
      refine ⟨eqv, ?_⟩
      unfold resp_rel
      intro x₀ x₁
      rw [eq]
      exact h.resp_rel
    exfalso
    apply g
    apply Nonempty.intro
    apply h.congr
    assumption
    symm; assumption
    apply Nonempty.intro
    refine ⟨h.toRelEmbedding, ?_⟩
    assumption
  le_refl a := by
    induction a using ind
    exact ⟨InitialSegment.refl _⟩
  le_trans := by
    intro a b c
    induction a, b, c using ind₃
    intro ⟨ab⟩ ⟨bc⟩
    exact ⟨ab.trans bc⟩
  le_antisymm := by
    intro a b
    induction a, b using ind₂
    intro ⟨ab⟩ ⟨ba⟩
    apply sound
    apply InitialSegment.antisymm <;> assumption

instance : @Relation.IsWellOrder Nat (· < ·) where
  wf := Nat.lt_wfRel.wf
  trans := Nat.lt_trans
  tri := Nat.lt_trichotomy

def Pre.ofNat (n: Nat) : Pre where
  ty := Fin n
  rel a b := a < b
  wo := Fin.relEmbedNat.wo

def Ordinal.ofNat (n: Nat) := ⟦Pre.ofNat n⟧

instance : OfNat Pre n := ⟨(Pre.ofNat n).lift⟩
instance : OfNat Ordinal n := ⟨(Ordinal.ofNat n).lift⟩

def Pre.typein {α: Type u} (r: α -> α -> Prop) [Relation.IsWellOrder r] (a: α) : Pre.{u} where
  ty := { x: α // r x a }
  rel x y := r x y
  wo := (Subtype.relEmbed r).wo

def typein (r: α -> α -> Prop) [Relation.IsWellOrder r] (a: α) : Ordinal := ⟦Pre.typein r a⟧

def typein_surj (r: α -> α -> Prop) [Relation.IsWellOrder r] : ∀o, o < type r -> ∃x: α, o = typein r x := by
  intro o lt
  induction o using ind with | mk o =>
  obtain ⟨lt⟩ := lt
  have ⟨top, spec⟩  := lt.exists_top
  exists top
  apply sound
  apply RelIso.mk
  case toEquiv =>
    apply Equiv.mk
    case toFun =>
      intro x
      refine ⟨lt x, ?_⟩
      apply (spec _).mpr
      apply Set.mem_range'
    case invFun =>
      intro ⟨val, lt_top⟩
      exact Classical.choose <| Set.mem_range.mp <| (spec val).mp lt_top
    case rightInv =>
      intro ⟨a, lt_top⟩
      dsimp
      congr
      exact (Classical.choose_spec <| Set.mem_range.mp <| (spec a).mp lt_top).symm
    case leftInv =>
      intro x
      dsimp
      apply lt.inj
      refine (Classical.choose_spec <| Set.mem_range.mp <| (spec _).mp ?_).symm
      exact (spec (lt x)).mpr Set.mem_range'
  case resp_rel =>
    exact lt.resp_rel

def Pre.typein_lt (r: α -> α -> Prop) (a) [Relation.IsWellOrder r] : (typein r a).rel ≺i r := by
  apply PrincipalSegment.mk _ _
  exact Subtype.relEmbed r
  exists a
  intro b
  apply Iff.intro
  intro h
  apply Set.mem_range.mpr
  exact ⟨⟨b, h⟩, rfl⟩
  intro mem
  obtain ⟨⟨b, h⟩, eq⟩ := Set.mem_range.mp mem
  subst eq
  assumption

def typein_lt (r: α -> α -> Prop) (a) [Relation.IsWellOrder r] : (typein r a) < type r := by
  apply Nonempty.intro
  apply Pre.typein_lt

open Classical in
def typein_lt_typein_iff [Relation.IsWellOrder r] : typein r a < typein r b ↔ r a b := by
  have := (Subtype.relEmbed (P := fun x => r x b) r).wo
  have := (Subtype.relEmbed (P := fun x => r x a) r).wo
  apply Iff.intro
  · intro ⟨h⟩
    let rb_lt_r := Pre.typein_lt r b
    let ra_lt_r := Pre.typein_lt r a
    have a_princ_top_ra_lt_r : ra_lt_r.IsPrincipalTop a := by
      intro x
      rw [Set.mem_range]
      apply Iff.intro
      intro g
      exists ⟨x, g⟩
      intro ⟨x', eq⟩
      subst x
      exact x'.property
    let ra_lt_r' := PrincipalSegment.trans h rb_lt_r
    have : ra_lt_r = ra_lt_r' := Subsingleton.allEq _ _
    rw [this] at a_princ_top_ra_lt_r
    obtain ⟨top, spec⟩  := h.exists_top
    have : ra_lt_r'.IsPrincipalTop top := h.top_of_lt_of_lt_of_le (rb_lt_r: (Pre.typein r b).rel ≼i r) top spec
    have := PrincipalSegment.top_unique' ra_lt_r' _ _ a_princ_top_ra_lt_r this
    subst a
    exact top.property
  · intro h
    apply Nonempty.intro
    refine ⟨⟨⟨?_, ?_⟩ , ?_⟩ , ?_⟩
    intro ⟨x, g⟩
    exact ⟨x, Relation.trans g h⟩
    intro ⟨_, _⟩ ⟨_, _⟩ eq
    cases eq
    congr
    rfl
    dsimp
    exists ⟨a, h⟩
    intro ⟨c, g⟩
    dsimp
    rw [Set.mem_range]
    apply Iff.intro
    intro g
    exact ⟨⟨_, g⟩, rfl⟩
    intro ⟨⟨c, g⟩, eq⟩
    cases eq
    assumption

def lt_wf : @WellFounded Ordinal (· < ·) := by
  apply WellFounded.intro
  intro a
  apply Acc.intro
  intro b r
  induction a using ind with | mk a =>
  obtain ⟨α, rel, wo⟩ := a
  have ⟨a₀, eq⟩ := typein_surj rel b r
  subst b
  clear r
  induction a₀ using (Relation.wellFounded rel).induction with
  | h a₀ ih =>
  apply Acc.intro
  intro c r
  have ⟨c₀, eq⟩  := typein_surj _ _ (lt_trans r (typein_lt _ _))
  subst eq
  apply ih
  apply typein_lt_typein_iff.mp r

instance : @Relation.IsWellFounded Ordinal (· < ·) := ⟨lt_wf⟩
instance : WellFoundedRelation Ordinal := ⟨_, lt_wf⟩

end Ordinal
