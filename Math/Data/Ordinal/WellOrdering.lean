import Math.Data.Ordinal.Basic
import Math.Order.Zorn

namespace WellOrdering

open Classical

private
structure SubWellOrder (α: Type*) where
  intro ::
  set: Set α
  rel: α -> α -> Prop
  wo: Relation.IsWellOrder (set.Induced rel)

private
structure SubWellOrder.LE (a b : SubWellOrder α) : Prop where
  sub: a.set ⊆ b.set
  resp_rel: ∀x y: a.set, a.rel x y ↔ b.rel x y
  init: ∀x: a.set, ∀y: (b.set \ a.set: Set _), b.rel x y

private
instance : LE (SubWellOrder α) where
  le := SubWellOrder.LE

private
instance : LT (SubWellOrder α) where
  lt a b := a ≤ b ∧ ¬b ≤ a

private
instance : IsPreOrder (SubWellOrder α) where
  lt_iff_le_and_not_le := Iff.rfl
  le_refl a := ⟨Set.sub_refl _, fun _ _ => Iff.rfl, fun x y => by
    rw [Set.sdiff_self] at y
    have := y.property
    contradiction⟩
  le_trans := by
    intro a b c ab bc
    refine ⟨Set.sub_trans ab.sub bc.sub, ?_, ?_⟩
    intro x y
    apply Iff.trans (ab.resp_rel _ _)
    apply bc.resp_rel ⟨_, _⟩ ⟨_, _⟩
    apply ab.sub
    exact x.property
    apply ab.sub
    exact y.property
    intro ⟨x, hx⟩ ⟨y, hy, hy'⟩
    dsimp
    by_cases hby:y ∈ b.set
    apply (bc.resp_rel ⟨_, _⟩ ⟨_, _⟩).mp (ab.init ⟨x, hx⟩ ⟨y, hby, hy'⟩)
    apply ab.sub; assumption
    assumption
    apply bc.init ⟨x, ab.sub _ hx⟩ ⟨y, hy, ?_⟩
    assumption

private def RelWithTop (r: α -> α -> Prop) (top: α) (a b: α): Prop :=
  if a = top then False
  else if b = top then True
  else r a b

private
def SubWellOrder.insert_wo (top: α) (s: Set α) (h: top ∉ s) {r: α -> α -> Prop} [Relation.IsWellOrder (s.Induced r)] :
  Relation.IsWellOrder ((insert top s).Induced (RelWithTop r top)) where
  wf := by
    apply WellFounded.intro
    intro ⟨a, mema⟩
    replace mema := Set.mem_insert.mp mema
    have : ∀x: s, Acc (Set.Induced (RelWithTop r top) (insert top s)) ⟨x, Set.mem_insert.mpr (.inr x.property)⟩ := by
      intro x
      induction x using Relation.wfInduction (Set.Induced r s) with
      | h x ih =>
      obtain ⟨x, mem⟩ := x
      apply Acc.intro
      intro y g
      unfold Set.Induced RelWithTop at g
      split at g
      contradiction
      split at g
      dsimp at *; subst x
      contradiction
      apply ih ⟨y.val, _⟩
      assumption
      have hy := y.property
      rw [Set.mem_insert] at hy
      apply hy.resolve_left _
      intro eq
      contradiction
    rcases mema with eq | mema
    · subst a
      apply Acc.intro
      intro ⟨b, memb⟩ g
      unfold Set.Induced RelWithTop at g
      dsimp at g
      split at g
      contradiction
      rename_i bne
      rw [Set.mem_insert] at memb
      replace memb := memb.resolve_left bne
      apply this ⟨_, _⟩
      assumption
    · apply this ⟨_, _⟩
      assumption
  trans := by
    unfold Set.Induced RelWithTop
    intro a b c ab bc
    by_cases ha:a.val=top
    rw [if_pos ha] at *
    contradiction
    rw [if_neg ha] at *
    by_cases hb:b.val=top
    rw [if_pos hb] at *
    contradiction
    rw [if_neg hb] at *
    by_cases hc:c.val=top
    rw [if_pos hc] at *
    trivial
    rw [if_neg hc] at *
    let a': s := ⟨a.val, ?_⟩
    let b': s := ⟨b.val, ?_⟩
    let c': s := ⟨c.val, ?_⟩
    show Set.Induced r s a' c'
    apply Relation.trans (r := Set.Induced r s)
    show Set.Induced r s a' b'
    exact ab
    exact bc
    apply (Set.mem_insert.mp c.property).resolve_left
    assumption
    apply (Set.mem_insert.mp b.property).resolve_left
    assumption
    apply (Set.mem_insert.mp a.property).resolve_left
    assumption
  tri := by
    intro ⟨a, ha⟩ ⟨b, hb⟩
    rw [Set.mem_insert] at ha hb
    unfold Set.Induced RelWithTop
    dsimp
    rcases ha <;> rcases hb
    subst a; subst b
    right; left; congr
    subst a
    right; right
    rw [if_neg, if_pos rfl]
    trivial
    intro h; subst b
    contradiction
    subst b
    left
    rw [if_neg, if_pos rfl]
    trivial
    intro h; subst a
    contradiction
    rename_i ha hb
    have nha: a ≠ top := by intro; subst a; contradiction
    have nhb: b ≠ top := by intro; subst b; contradiction
    rcases Relation.trichotomous (Set.Induced r s) ⟨a, ha⟩ ⟨b, hb⟩ with ab | eq | ba
    left; rwa [if_neg nha, if_neg nhb]
    cases eq; right; left; congr
    right; right; rwa [if_neg nha, if_neg nhb]

private
def SubWellOrder.sunion_rel (S: Set (SubWellOrder α)) (a b: α) : Prop :=
  ∃s ∈ S, a ∈ s.set ∧ b ∈ s.set ∧ s.rel a b

private
def SubWellOrder.total (S: Set (SubWellOrder α)) (h: S.IsChain (· ≤ ·)) : ∀a b: S, a.val ≤ b.val ∨ b.val ≤ a.val := by
  intro a b
  rcases h.tri a b with le | eq | ge
  left; assumption
  left; rw [eq]
  right; assumption

private
def SubWellOrder.sUnion_wo (S: Set (SubWellOrder α)) (h: S.IsChain (· ≤ ·)) :
  Relation.IsWellOrder ((⋃S.image SubWellOrder.set).Induced (SubWellOrder.sunion_rel S)) where
  wf := by
    apply WellFounded.intro
    intro ⟨x, _, ⟨s, mem_in_S, eq⟩, hx⟩
    subst eq
    have := s.wo
    have := Relation.wfInduction (C := fun x => Acc (Set.Induced (sunion_rel S) (⋃S.image set)) ⟨x.val, Set.mem_sUnion.mpr ⟨_, Set.mem_image.mpr ⟨_, mem_in_S, rfl⟩, x.property⟩⟩) (Set.Induced s.rel s.set)
    apply this ⟨_, _⟩ _; clear this
    assumption
    clear hx x this
    intro ⟨x, hx⟩ ih
    apply Acc.intro
    intro ⟨y, hy⟩ ⟨s', s'_in_S, y_in_s', x_in_s', hxy⟩
    dsimp at *
    rcases total S h ⟨_, mem_in_S⟩ ⟨_, s'_in_S⟩ with ss' | s's
    · by_cases hy':y ∈ s.set
      apply ih ⟨_, _⟩
      unfold Set.Induced; dsimp;
      apply (ss'.resp_rel ⟨_, _⟩ ⟨_, _⟩).mpr
      repeat assumption
      have := ss'.init ⟨_, hx⟩ ⟨_, y_in_s', hy'⟩
      dsimp at this
      have _ := s'.wo
      have := Relation.asymm (r := Set.Induced s'.rel s'.set) (a := ⟨_, x_in_s'⟩) (b := ⟨_, y_in_s'⟩) this hxy
      contradiction
    · have := s's.sub _ y_in_s'
      apply ih ⟨_, _⟩
      unfold Set.Induced; dsimp;
      apply (s's.resp_rel ⟨_, _⟩ ⟨_, _⟩).mp
      repeat assumption
  trans := by
    intro a b c ⟨s₀, s₀_in_S, as₀, bs₀, ab⟩ ⟨s₁, s₁_in_S, bs₁, cs₁, bc⟩
    rcases total S h ⟨_, s₀_in_S⟩ ⟨_, s₁_in_S⟩ with le | ge
    · dsimp at le
      refine ⟨_, s₁_in_S, ?_, ?_,? _⟩
      apply le.sub; assumption
      assumption
      apply s₁.wo.trans (a := ⟨_, _⟩) (b := ⟨_, _⟩) (c := ⟨_, _⟩) _ bc
      apply le.sub; assumption
      assumption
      assumption
      apply (le.resp_rel ⟨_, _⟩ ⟨_, _⟩).mp
      assumption
      assumption
      assumption
    · dsimp at ge
      refine ⟨_, s₀_in_S, ?_, ?_,? _⟩
      assumption
      apply ge.sub; assumption
      apply s₀.wo.trans (a := ⟨_, _⟩) (b := ⟨_, _⟩) (c := ⟨_, _⟩) ab _
      assumption
      apply ge.sub; assumption
      apply ge.sub; assumption
      apply (ge.resp_rel ⟨_, _⟩ ⟨_, _⟩).mp
      assumption
      assumption
      assumption
  tri := by
    intro ⟨a, _, ⟨s₀, s₀_in_S, eqa⟩, ha⟩ ⟨b, _, ⟨s₁, s₁_in_S, eqb⟩, hb⟩
    subst eqa; subst eqb
    unfold Set.Induced sunion_rel
    dsimp
    rcases total S h ⟨_, s₀_in_S⟩ ⟨_, s₁_in_S⟩ with le | ge
    · dsimp at le
      rcases s₁.wo.tri ⟨a, le.sub _ ha⟩ ⟨b, hb⟩ with lt | eq | gt
      left
      refine ⟨_, s₁_in_S, ?_, ?_,? _⟩
      apply le.sub; assumption
      assumption
      assumption
      cases eq
      right; left; rfl
      right; right;
      refine ⟨_, s₁_in_S, ?_, ?_,? _⟩
      assumption
      apply le.sub; assumption
      assumption
    · dsimp at ge
      rcases s₀.wo.tri ⟨a, ha⟩ ⟨b, ge.sub _ hb⟩ with lt | eq | gt
      left
      refine ⟨_, s₀_in_S, ?_, ?_,? _⟩
      assumption
      apply ge.sub; assumption
      assumption
      cases eq
      right; left; rfl
      right; right;
      refine ⟨_, s₀_in_S, ?_, ?_,? _⟩
      apply ge.sub; assumption
      assumption
      assumption

def SubWellOrder.exists_wo (α: Type*) : ∃r: α -> α -> Prop, Relation.IsWellOrder r := by
  have ⟨⟨s, r, h⟩, spec⟩ := Zorn.preorder (α := SubWellOrder α) ?_
  suffices s = ⊤ by
    subst s
    exists r
    suffices r ↪r Set.Induced r ⊤ from this.wo
    refine ⟨⟨?_, ?_⟩, ?_⟩
    intro x
    exact ⟨x, True.intro⟩
    intro x y eq
    cases eq
    rfl
    rfl
  · apply Set.ext_univ
    intro top
    apply Classical.byContradiction
    intro mem
    let swo : SubWellOrder α := ⟨insert top s, RelWithTop r top, SubWellOrder.insert_wo _ _ mem⟩
    have := spec swo ⟨Set.sub_insert, fun x y => ?_, ?_⟩
    have := Set.sub_antisymm this.sub Set.sub_insert
    have : top ∈ s := by
      dsimp at this
      rw [←this, Set.mem_insert]
      left; rfl
    contradiction
    show _ ↔ RelWithTop _ _ _ _
    unfold RelWithTop
    apply Iff.intro
    · intro hxy
      rw [if_neg, if_neg]
      assumption
      intro
      subst top
      have := y.property
      contradiction
      intro
      subst top
      have := x.property
      contradiction
    · intro hxy
      rw [if_neg, if_neg] at hxy
      assumption
      intro h; subst top
      have := y.property
      contradiction
      intro h; subst top
      have := x.property
      contradiction
    · intro ⟨x, hx⟩ ⟨y, hy, hy'⟩
      dsimp
      replace hy: y ∈ insert _ _ := hy
      rw [Set.mem_insert] at hy
      cases hy
      subst y
      show RelWithTop _ _ _ _
      unfold RelWithTop
      rw [if_neg, if_pos rfl]
      trivial
      intro h
      subst x
      contradiction
      contradiction
  · intro S c
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    exact ⋃S.image SubWellOrder.set
    exact SubWellOrder.sunion_rel S
    exact SubWellOrder.sUnion_wo S c
    intro s mem
    refine ⟨?_, ?_, ?_⟩
    · apply Set.sub_sUnion
      apply Set.mem_image'
      assumption
    · intro x y
      apply Iff.intro
      · intro r
        dsimp
        exists s
        refine ⟨?_, ?_, ?_, ?_⟩
        assumption
        exact x.property
        exact y.property
        assumption
      · intro ⟨s', s'_in_S, hx, hy, hxy⟩
        rcases c.tri ⟨_, mem⟩ ⟨_, s'_in_S⟩ with rxy | eq | ryx
        · apply (rxy.resp_rel _ _).mpr
          assumption
        · cases eq
          assumption
        · apply (ryx.resp_rel ⟨_, _⟩ ⟨_, _⟩).mp
          assumption
          assumption
          assumption
    · intro ⟨x, hx⟩ ⟨y, hy, hy'⟩
      dsimp at hy
      dsimp [SubWellOrder.sunion_rel]
      obtain ⟨_, ⟨s', s'_in_S, eq⟩, hy⟩ := hy
      subst eq
      rcases total S c ⟨s', s'_in_S⟩ ⟨s, mem⟩ with le | ge
      have := le.sub _ hy
      contradiction
      dsimp at ge
      refine ⟨_, s'_in_S, ?_, ?_, ?_⟩
      · apply ge.sub
        assumption
      · assumption
      · apply ge.init ⟨_, _⟩ ⟨_, _, _⟩
        assumption
        assumption
        assumption

def order (α: Type*): α -> α -> Prop := choose (SubWellOrder.exists_wo α)
instance : Relation.IsWellOrder (order α) := choose_spec (SubWellOrder.exists_wo α)

end WellOrdering
