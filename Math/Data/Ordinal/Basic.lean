import Math.Relation.Basic
import Math.Relation.RelIso
import Math.Tactics.PPWithUniv
import Math.Relation.Segments
import Math.Order.Linear
import Math.AxiomBlame
import Math.Data.Quotient.Basic
import Math.Data.Set.Order.Bounds
import Math.Data.Fintype.Basic

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
scoped notation "⟦" x "⟧" => Ordinal.mk x
@[cases_eliminator]
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

instance : CoeSort Ordinal (Type _) where
  coe a := { x // x < a }

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

def Pre.zero : Pre where
  ty := PEmpty
  rel := nofun
  wo := {
    trans := fun {x} => x.elim
    tri := fun {x} => x.elim
    wf := ⟨fun {x} => x.elim⟩
  }

def Pre.one : Pre where
  ty := PUnit
  rel _ _ := False
  wo := {
    trans := fun x => x.elim
    tri := fun  _ _ => .inr (.inl rfl)
    wf := by
      refine ⟨?_⟩
      intro x
      apply Acc.intro
      intro y f
      contradiction
  }

def zero : Ordinal := ⟦Pre.zero⟧
def one : Ordinal := ⟦Pre.one⟧

def Pre.ofNat (n: Nat) : Pre where
  ty := Fin n
  rel a b := a < b
  wo := Fin.relEmbedNat.wo

def ofNat (n: Nat) := ⟦Pre.ofNat n⟧

instance : NatCast Pre where
  natCast x := (Pre.ofNat x).lift

instance : NatCast Ordinal where
  natCast x := (ofNat x).lift

instance : OfNat Pre n := ⟨n⟩
instance : OfNat Ordinal n := ⟨n⟩

instance : IsEmpty (Pre.ofNat 0).ty := inferInstanceAs (IsEmpty (Fin 0))
instance : IsEmpty Pre.zero.ty := inferInstanceAs (IsEmpty PEmpty)
instance (p: Pre) [IsEmpty p.ty] : IsEmpty p.lift.ty := inferInstanceAs (IsEmpty (ULift p.ty))

instance : Inhabited Pre.one.ty := inferInstanceAs (Inhabited PUnit)
instance : Inhabited (Pre.ofNat 1).ty := inferInstanceAs (Inhabited (Fin 1))
instance [Inhabited α] : Inhabited (ULift α) where
  default := ⟨default⟩
instance (p: Pre) [Inhabited p.ty] : Inhabited p.lift.ty := inferInstanceAs (Inhabited (ULift p.ty))
instance : Subsingleton Pre.one.ty := inferInstanceAs (Subsingleton PUnit)
instance : Subsingleton (Pre.ofNat 1).ty := inferInstanceAs (Subsingleton (Fin 1))
instance (p: Pre) [Subsingleton p.ty] : Subsingleton p.lift.ty := inferInstanceAs (Subsingleton (ULift p.ty))

def zero_eq : 0 = zero := by
  apply sound
  apply empty_reliso_empty

def one_eq : 1 = one := by
  apply sound
  refine ⟨?_, ?_⟩
  apply unique_eq_unique
  intro a b
  apply Iff.intro
  intro h
  rw [Subsingleton.allEq a b] at h
  exact Fin.lt_irrefl _ h
  intro
  contradiction

instance (p: Pre) : WellFoundedRelation p.ty where
  rel := p.rel
  wf := p.wo.wf

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

def Pre.typein_top (r: α -> α -> Prop) (a) [Relation.IsWellOrder r] : (Subtype.relEmbed r (P := fun x => r x a)).IsPrincipalTop a := by
  intro b
  apply Iff.intro
  intro h
  apply Set.mem_range.mpr
  exact ⟨⟨b, h⟩, rfl⟩
  intro mem
  obtain ⟨⟨b, h⟩, eq⟩ := Set.mem_range.mp mem
  subst eq
  assumption

def Pre.typein_lt (r: α -> α -> Prop) (a) [Relation.IsWellOrder r] : (typein r a).rel ≺i r := by
  apply PrincipalSegment.mk _ _
  exact Subtype.relEmbed r
  exists a
  apply Pre.typein_top

def typein_lt (r: α -> α -> Prop) (a) [Relation.IsWellOrder r] : (typein r a) < type r := by
  apply Nonempty.intro
  apply Pre.typein_lt

def typein_lt_typein_iff [Relation.IsWellOrder r] : typein r a < typein r b ↔ r a b := by
  have := (Subtype.relEmbed (P := fun x => r x b) r).wo
  have := (Subtype.relEmbed (P := fun x => r x a) r).wo
  apply Iff.intro
  · intro ⟨h⟩
    let rb_lt_r := Pre.typein_lt r b
    let ra_lt_r := Pre.typein_lt r a
    have a_princ_top_ra_lt_r : ra_lt_r.IsPrincipalTop a := Pre.typein_top _ _
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

def typein_inj (r: α -> α -> Prop) [Relation.IsWellOrder r] : Function.Injective (typein r) := by
  intro x y eq
  replace ⟨eq⟩ := Quotient.exact eq
  dsimp [Pre.typein] at eq
  apply PrincipalSegment.top_unique (t := r)
  assumption
  case f =>
    apply PrincipalSegment.mk (Subtype.relEmbed _)
    exists x
    apply Pre.typein_top _ _
  case g =>
    apply PrincipalSegment.mk (Subtype.relEmbed _)
    exists y
    apply Pre.typein_top _ _
  case a =>
    apply Pre.typein_top _ _
  case a =>
    apply Pre.typein_top _ _

def typein_congr {r: α -> α -> Prop} {s: β -> β -> Prop} [Relation.IsWellOrder r] [Relation.IsWellOrder s] {a: α}
  (eq: r ≃r s) : typein s (eq a) = typein r a := by
  apply sound
  unfold Pre.typein
  dsimp
  refine ⟨⟨?_, ?_, ?_, ?_⟩ , ?_⟩
  intro ⟨x, sx⟩
  refine ⟨eq.symm x, ?_⟩
  rw [←eq.coe_symm a]
  apply eq.inv_resp_rel.mp
  assumption
  intro ⟨x, rx⟩
  refine ⟨eq x, ?_⟩
  apply eq.resp_rel.mp
  assumption
  intro ⟨x, sx⟩
  dsimp; congr
  rw [eq.symm_coe]
  intro ⟨x, sx⟩
  dsimp; congr
  rw [eq.coe_symm]
  exact eq.symm.resp_rel

def typein_congr_initial {r: α -> α -> Prop} {s: β -> β -> Prop} [rwo: Relation.IsWellOrder r] [swo: Relation.IsWellOrder s]
  (init: r ≼i s) {a: α} : typein s (init a) = typein r a := by
  apply sound; symm
  unfold Pre.typein
  dsimp
  refine ⟨⟨?_, ?_, ?_, ?_⟩ , ?_⟩
  intro ⟨x, rxa⟩
  refine ⟨?_, ?_⟩
  exact init x
  apply init.resp_rel.mp
  assumption
  intro ⟨x, sx⟩
  have mem := Set.mem_range.mp <| init.isInitial _ _ sx
  refine ⟨?_, ?_⟩
  exact Classical.choose mem
  apply init.resp_rel.mpr
  show s (init _) (init _)
  have : x = init _ := Classical.choose_spec mem
  rw [←this]
  assumption
  · intro ⟨x, rxa⟩
    dsimp
    congr
    have mem := Set.mem_range.mp <| init.isInitial _ _ (init.resp_rel.mp rxa)
    apply init.inj
    exact (Classical.choose_spec mem).symm
  · intro ⟨x, sxa⟩
    dsimp
    have mem := Set.mem_range.mp <| init.isInitial _ _ sxa
    congr
    exact (Classical.choose_spec mem).symm
  exact init.resp_rel

def typein_inj_initial {r: α -> α -> Prop} {s: β -> β -> Prop} [Relation.IsWellOrder r] [Relation.IsWellOrder s] {a: α} {b: β}
  (init: r ≼i s) : typein r a = typein s b -> b = init a := by
  intro eq
  rw [←typein_congr_initial init] at eq
  exact (typein_inj _ eq).symm

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

def Pre.minType (a b: Pre) := { x: a.ty × b.ty // Ordinal.typein a.rel x.fst = Ordinal.typein b.rel x.snd }

def Pre.minTypeRelEmbed : (fun x y: Pre.minType a b => a.rel x.val.fst y.val.fst) ↪r a.rel where
  toFun x := x.val.fst
  resp_rel := Iff.rfl
  inj := by
    intro ⟨⟨x₀, x₁⟩, xordeq⟩ ⟨⟨y₀, y₁⟩, yordeq⟩ eq
    dsimp at eq
    cases eq
    congr
    dsimp at xordeq
    dsimp at yordeq
    exact typein_inj _ <| xordeq.symm.trans yordeq

def Pre.min (a b: Pre) : Pre where
  ty := minType a b
  rel x y := a.rel x.val.fst y.val.fst
  wo := Pre.minTypeRelEmbed.wo

def Pre.min.spec (a b c d: Pre) (ac: a.rel ≃r c.rel) (bd:  b.rel ≃r d.rel): (a.min b).rel ≃r (c.min d).rel where
  toFun | ⟨⟨a₀, b₀⟩, ordeq⟩ => ⟨⟨ac a₀, bd b₀⟩, by
    dsimp at *
    rw [typein_congr, typein_congr]
    assumption⟩
  invFun | ⟨⟨c₀, d₀⟩, ordeq⟩ => ⟨⟨ac.symm c₀, bd.symm d₀⟩, by
    dsimp at *
    rw [typein_congr, typein_congr]
    assumption⟩
  leftInv := by
    intro ⟨⟨a₀, b₀⟩, ordeq⟩
    dsimp
    congr
    rw [ac.coe_symm]
    rw [bd.coe_symm]
  rightInv := by
    intro ⟨⟨c₀, d₀⟩, ordeq⟩
    dsimp
    congr
    rw [ac.symm_coe]
    rw [bd.symm_coe]
  resp_rel := by
    intro ⟨⟨a₀, b₀⟩, ordeq₀⟩ ⟨⟨a₁, b₁⟩, ordeq₁⟩
    exact ac.resp_rel

def min' : Ordinal -> Ordinal -> Ordinal := by
  apply Quotient.lift₂ (fun a b => ⟦a.min b⟧)
  intro a b c d ⟨ac⟩ ⟨bd⟩
  apply sound
  apply Pre.min.spec <;> assumption

instance : Min Ordinal := ⟨min'⟩

def min_comm' (a b: Ordinal) : min a b = min' b a := by
  induction a, b using ind₂ with | mk a b =>
  apply sound
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  intro ⟨⟨a₀, b₀⟩, ordeq⟩
  exact ⟨⟨b₀, a₀⟩, ordeq.symm⟩
  intro ⟨⟨b₀, a₀⟩, ordeq⟩
  exact ⟨⟨a₀, b₀⟩, ordeq.symm⟩
  intro ⟨⟨a₀, b₀⟩, ordeq⟩
  rfl
  intro ⟨⟨b₀, a₀⟩, ordeq⟩
  rfl
  intro ⟨⟨a₀, b₀⟩, ordeq₀⟩ ⟨⟨a₁, b₁⟩, ordeq₁⟩
  dsimp
  unfold Pre.min
  dsimp
  dsimp at ordeq₀ ordeq₁
  apply Iff.intro
  intro ha
  have := typein_lt_typein_iff.mpr ha
  rw [ordeq₀, ordeq₁] at this
  apply typein_lt_typein_iff.mp
  assumption
  intro hb
  have := typein_lt_typein_iff.mpr hb
  rw [←ordeq₀, ←ordeq₁] at this
  apply typein_lt_typein_iff.mp
  assumption

def min_eq_left_iff {a b: Ordinal} : a ≤ b ↔ min a b = a := by
  induction a, b using ind₂ with | mk a b =>
  apply Iff.intro
  · intro ⟨h⟩
    apply sound
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    intro ⟨x, _⟩
    exact x.fst
    intro a₀
    refine ⟨⟨a₀, h a₀⟩, ?_⟩
    dsimp
    symm
    apply typein_congr_initial
    intro ⟨⟨a₀, b₀⟩, g⟩
    dsimp; congr
    dsimp at g
    exact (typein_inj_initial h g).symm
    intro x
    rfl
    rfl
  · intro h
    rw [←h, min_comm']
    clear h
    apply Nonempty.intro
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    intro x
    exact x.val.fst
    intro x y eq
    dsimp at eq
    have : x.val.snd = y.val.snd := by
      apply typein_inj a.rel
      rw [←x.property, ←y.property, eq]
    exact Subtype.embed.inj <| Prod.ext eq this
    rfl
    intro x y h
    replace h : b.rel y x.val.fst := h
    apply Set.mem_range.mpr
    have ⟨g⟩ := Quotient.exact x.property
    refine ⟨⟨⟨y, (g ⟨_, h⟩).val⟩, ?_⟩, ?_⟩
    dsimp
    have: typein _ (g ⟨y, h⟩) = typein (Pre.typein _ _).rel (Subtype.mk y h) := typein_congr_initial g.toInitial
    let ainit := Subtype.initalSegment a.rel (P := fun y => a.rel y x.val.snd) <| by
      intro a₀ a₁
      exact flip Relation.trans
    let binit := Subtype.initalSegment b.rel (P := fun y => b.rel y x.val.fst) <| by
      intro a₀ a₁
      exact flip Relation.trans
    have awo := ainit.wo
    have bwo := binit.wo
    have : typein b.rel y = _ := typein_congr_initial binit (rwo := inferInstance) (swo := inferInstance) (a := ⟨y, h⟩)
    rw [this]; clear this
    have : typein a.rel (g ⟨y, h⟩).val  = _ := typein_congr_initial ainit (rwo := inferInstance) (swo := inferInstance) (a := (g ⟨y, h⟩))
    rw [this]; clear this
    exact (typein_congr g (a := ⟨y, h⟩) (r := (Pre.typein b.rel _).rel)).symm
    rfl

def Pre.add (a b: Pre) : Pre where
  ty := a.ty ⊕ b.ty
  rel := Sum.Lex a.rel b.rel

def Pre.mul (a b: Pre) : Pre where
  ty := a.ty × b.ty
  rel := Prod.Lex a.rel b.rel

def Pre.add.spec (a b c d: Pre) (ac: a.rel ≃r c.rel) (bd: b.rel ≃r d.rel) : Sum.Lex a.rel b.rel ≃r Sum.Lex c.rel d.rel where
  toEquiv := Sum.equivCongr ac.toEquiv bd.toEquiv
  resp_rel := by
    intro x y
    cases x <;> cases y <;> rename_i x y
    all_goals apply Iff.intro
    all_goals intro h
    any_goals contradiction
    any_goals apply Sum.Lex.sep
    any_goals apply Sum.Lex.inl
    any_goals apply Sum.Lex.inr
    any_goals cases h
    apply ac.resp_rel.mp; assumption
    apply ac.resp_rel.mpr; assumption
    apply bd.resp_rel.mp; assumption
    apply bd.resp_rel.mpr; assumption

def Pre.mul.spec (a b c d: Pre) (ac: a.rel ≃r c.rel) (bd: b.rel ≃r d.rel) : Prod.Lex a.rel b.rel ≃r Prod.Lex c.rel d.rel where
  toEquiv := Prod.equivCongr ac.toEquiv bd.toEquiv
  resp_rel := by
    intro x y
    cases x <;> cases y <;> rename_i x y
    all_goals apply Iff.intro
    all_goals intro h
    any_goals cases h
    apply Prod.Lex.left
    apply ac.resp_rel.mp; assumption
    apply Prod.Lex.right
    apply bd.resp_rel.mp; assumption
    unfold Prod.equivCongr Prod.equivSigma Sigma.equivCongr
      Sigma.equivPSigma PSigma.equivCongr Equiv.trans Equiv.symm at h
    dsimp at h
    rename_i a₀ b₀
    generalize ha₁:ac.toFun a₀=a₁
    generalize hb₁:bd.toFun b₀=b₁
    rw [ha₁, hb₁] at h
    cases h
    apply Prod.Lex.left
    subst a₁; subst b₁
    apply ac.resp_rel.mpr; assumption
    cases ac.toFun_inj ha₁
    apply Prod.Lex.right
    subst b₁
    apply bd.resp_rel.mpr; assumption

def add : Ordinal -> Ordinal -> Ordinal := by
  apply Quotient.lift₂ (fun a b => ⟦a.add b⟧)
  intro a b c d ⟨ac⟩ ⟨bd⟩
  apply sound
  apply Pre.add.spec <;> assumption

def mul : Ordinal -> Ordinal -> Ordinal := by
  apply Quotient.lift₂ (fun a b => ⟦a.mul b⟧)
  intro a b c d ⟨ac⟩ ⟨bd⟩
  apply sound
  apply Pre.mul.spec <;> assumption

instance : Add Ordinal := ⟨add⟩
instance : Mul Ordinal := ⟨mul⟩

def le_total_of_le (o: Ordinal) : ∀a b, a ≤ o -> b ≤ o -> a ≤ b ∨ b ≤ a := by
  suffices ∀a b, a < o -> b < o -> a ≤ b ∨ b ≤ a by
    intro a b ao bo
    rcases lt_or_eq_of_le ao with ao | a_eq_o <;> rcases lt_or_eq_of_le bo with bo | b_eq_o
    apply this <;> assumption
    subst b
    left; assumption
    subst a
    right; assumption
    subst a; subst b
    left; rfl
  intro a b ao bo
  cases o with | mk o =>
  have ⟨a, eq⟩ := typein_surj o.rel a ao
  subst eq
  have ⟨b, eq⟩ := typein_surj o.rel b bo
  subst eq
  rcases Relation.trichotomous o.rel a b with ab | eq | ba
  left; apply le_of_lt; apply typein_lt_typein_iff.mpr; assumption
  left; rw [eq]
  right; apply le_of_lt; apply typein_lt_typein_iff.mpr; assumption

def le_add_left (a b: Ordinal) : a ≤ a + b := by
  induction a, b using ind₂ with | mk a b =>
  apply Nonempty.intro
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  exact .inl
  apply Sum.inl.inj
  intro x y
  apply Iff.intro
  exact Sum.Lex.inl
  intro h
  cases h
  assumption
  intro x y h
  cases h
  apply Set.mem_range'

def le_add_right (a b: Ordinal) : b ≤ a + b := by
  induction a, b using ind₂ with | mk a b =>
  apply InitialSegment.collapse
  refine ⟨?_⟩
  refine ⟨⟨.inr, ?_⟩, ?_⟩
  apply Sum.inr.inj
  intro x y
  apply Iff.intro
  exact Sum.Lex.inr
  intro h
  cases h
  assumption

instance : IsLinearOrder Ordinal where
  lt_iff_le_and_not_le := lt_iff_le_and_not_le
  le_antisymm := le_antisymm
  le_trans := le_trans
  lt_or_le := by
    intro a b
    rcases le_total_of_le (a + b) a b (le_add_left _ _) (le_add_right _ _) with ab | ba
    rcases lt_or_eq_of_le ab with ab | eq
    left; assumption
    right; rw [eq]
    right; assumption

inductive Pre.maxType {α β: Type u}
  (r: α -> α -> Prop) (s: β -> β -> Prop)
  [Relation.IsWellOrder r] [Relation.IsWellOrder s] where
| inl (a: α) (h: ∀b, Ordinal.typein s b < Ordinal.typein r a)
| inr (b: β) (h: ∀a, Ordinal.typein r a < Ordinal.typein s b)
| mk  (a: α) (b: β) (h: Ordinal.typein r a = Ordinal.typein s b)

namespace Pre.maxType

variable {r: α -> α -> Prop} {s: β -> β -> Prop} [Relation.IsWellOrder r] [Relation.IsWellOrder s]

def not_inl_and_inr
  (a: α) (ha: ∀b₀, Ordinal.typein s b₀ < Ordinal.typein r a)
  (b: β) (hb: ∀a₀, Ordinal.typein r a₀ < Ordinal.typein s b):
  False := lt_irrefl <| lt_trans (ha b) (hb a)

inductive LT : Pre.maxType r s -> Pre.maxType r s -> Prop where
| inl : r a₀ a₁ -> LT (.inl a₀ h₀) (.inl a₁ h₁)
| mk : r a₀ a₁ -> LT (.mk a₀ b₀ h₀) (.mk a₁ b₁ h₁)
| inr : s b₀ b₁ -> LT (.inr b₀ h₀) (.inr b₁ h₁)
| mk_inl : LT (mk _ _ _) (inl _ _)
| mk_inr : LT (mk _ _ _) (inr _ _)

def mk_acc : Acc Pre.maxType.LT (maxType.mk (r := r) (s := s) a b h) := by
  induction a using Relation.wfInduction r generalizing b with
  | h a ih =>
  apply Acc.intro
  intro _ lt
  cases lt with
  | mk =>
  apply ih
  assumption

def inl_acc : Acc Pre.maxType.LT (maxType.inl (r := r) (s := s) a h) := by
  induction a using Relation.wfInduction r with
  | h a ih =>
  apply Acc.intro
  intro b lt
  cases lt with
  | mk_inl => apply mk_acc
  | inl =>
    rename_i a' ha' ha lt
    apply ih
    assumption
def inr_acc : Acc Pre.maxType.LT (maxType.inr (r := r) (s := s) b h) := by
  induction b using Relation.wfInduction s with
  | h a ih =>
  apply Acc.intro
  intro b lt
  cases lt with
  | mk_inr => apply mk_acc
  | inr =>
    rename_i a' ha' ha lt
    apply ih
    assumption

instance : Relation.IsWellOrder (Pre.maxType.LT (r := r) (s := s)) where
  trans := by
    intro a b c ab bc
    cases ab <;> cases bc
    any_goals apply LT.mk_inl
    any_goals apply LT.mk_inr
    apply LT.inl
    apply Relation.trans <;> assumption
    apply LT.mk
    apply Relation.trans <;> assumption
    apply LT.inr
    apply Relation.trans <;> assumption
  tri := by
    intro a b
    cases a <;> cases b
    any_goals
      rename_i ha _ hb
      have := not_inl_and_inr _ ha _ hb
      contradiction
    rename_i a _ b _
    rcases Relation.trichotomous r a b with ab | eq | ba
    left; apply LT.inl; assumption
    right; left; congr
    right; right; apply LT.inl; assumption
    right; right; apply LT.mk_inl
    rename_i a _ b _
    rcases Relation.trichotomous s a b with ab | eq | ba
    left; apply LT.inr; assumption
    right; left; congr
    right; right; apply LT.inr; assumption
    right; right; apply LT.mk_inr
    left; apply LT.mk_inl
    left; apply LT.mk_inr
    rename_i a _ ha b _ hb
    rcases Relation.trichotomous r a b with ab | eq | ba
    left; apply LT.mk; assumption
    right; left; congr
    rw [←eq, ha] at hb
    exact typein_inj s hb
    right; right; apply LT.mk; assumption
  wf := by
    apply WellFounded.intro
    intro x
    cases x
    apply inl_acc
    apply inr_acc
    apply mk_acc

end Pre.maxType

def Pre.max (a b: Pre) : Pre where
  ty := Pre.maxType a.rel b.rel
  rel := Pre.maxType.LT

def Pre.max.spec (a b c d: Pre) (ac: a.rel ≃r c.rel) (bd: b.rel ≃r d.rel) : (a.max b).rel ≃r (c.max d).rel := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x
    match x with
    | .mk a₀ b₀ eq =>
      refine .mk (ac a₀) (bd b₀) ?_
      rw [Ordinal.typein_congr ac, Ordinal.typein_congr bd]
      assumption
    | .inl a₀ h =>
      refine .inl (ac a₀) ?_
      intro d₀
      rw [Ordinal.typein_congr ac, ←Ordinal.typein_congr bd.symm]
      apply h
    | .inr b₀ h =>
      refine .inr (bd b₀) ?_
      intro c₀
      rw [←Ordinal.typein_congr ac.symm, Ordinal.typein_congr bd]
      apply h
  · intro x
    match x with
    | .mk a₀ b₀ eq =>
      refine .mk (ac.symm a₀) (bd.symm b₀) ?_
      rw [Ordinal.typein_congr ac.symm, Ordinal.typein_congr bd.symm]
      assumption
    | .inl a₀ h =>
      refine .inl (ac.symm a₀) ?_
      intro d₀
      rw [Ordinal.typein_congr ac.symm, ←Ordinal.typein_congr bd]
      apply h
    | .inr b₀ h =>
      refine .inr (bd.symm b₀) ?_
      intro c₀
      rw [←Ordinal.typein_congr ac, Ordinal.typein_congr bd.symm]
      apply h
  · intro x
    cases x <;> dsimp
    congr; rw [ac.coe_symm]
    congr; rw [bd.coe_symm]
    congr; rw [ac.coe_symm]; rw [bd.coe_symm]
  · intro x
    cases x <;> dsimp
    congr; rw [ac.symm_coe]
    congr; rw [bd.symm_coe]
    congr; rw [ac.symm_coe]; rw [bd.symm_coe]
  · dsimp
    intro x y
    apply Iff.intro
    · intro h
      cases h <;> dsimp
      apply maxType.LT.inl
      apply ac.resp_rel.mp
      assumption
      apply maxType.LT.mk
      apply ac.resp_rel.mp
      assumption
      apply maxType.LT.inr
      apply bd.resp_rel.mp
      assumption
      apply maxType.LT.mk_inl
      apply maxType.LT.mk_inr
    · intro h
      cases x <;> cases y <;> cases h
      apply maxType.LT.inl
      apply ac.resp_rel.mpr
      assumption
      apply maxType.LT.inr
      apply bd.resp_rel.mpr
      assumption
      apply maxType.LT.mk_inl
      apply maxType.LT.mk_inr
      apply maxType.LT.mk
      apply ac.resp_rel.mpr
      assumption

def max' : Ordinal -> Ordinal -> Ordinal := by
  apply Quotient.lift₂ (fun a b => ⟦a.max b⟧)
  intro a b c d ⟨ac⟩ ⟨bd⟩
  apply sound
  apply Pre.max.spec <;> assumption

instance : Max Ordinal := ⟨Ordinal.max'⟩

def max_comm' (a b: Ordinal) : max a b = max b a := by
  induction a, b using ind₂ with | mk a b =>
  apply sound
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x
    match x with
    | .mk a₀ b₀ eq =>
      refine .mk b₀ a₀ ?_
      symm; assumption
    | .inl a₀ h =>
      refine .inr a₀ ?_
      assumption
    | .inr b₀ h =>
      refine .inl b₀ ?_
      assumption
  · intro x
    match x with
    | .mk a₀ b₀ eq =>
      refine .mk b₀ a₀ ?_
      symm; assumption
    | .inl a₀ h =>
      refine .inr a₀ ?_
      assumption
    | .inr b₀ h =>
      refine .inl b₀ ?_
      assumption
  · intro x
    cases x <;> rfl
  · intro x
    cases x <;> rfl
  · dsimp
    intro x y
    apply Iff.intro
    · intro h
      cases h <;> dsimp
      apply Pre.maxType.LT.inr
      assumption
      apply Pre.maxType.LT.mk
      rename_i a₀ a₁ b₀ h₀ b₁ h₁ r
      have := typein_lt_typein_iff.mpr r
      rw [h₀, h₁] at this
      apply typein_lt_typein_iff.mp
      assumption
      apply Pre.maxType.LT.inl
      assumption
      apply Pre.maxType.LT.mk_inr
      apply Pre.maxType.LT.mk_inl
    · intro h
      cases x <;> cases y <;> cases h
      apply Pre.maxType.LT.inl
      assumption
      apply Pre.maxType.LT.inr
      assumption
      apply Pre.maxType.LT.mk_inl
      apply Pre.maxType.LT.mk_inr
      apply Pre.maxType.LT.mk
      rename_i a₀ a₁ b₀ b₁ h₀ h₁ r _
      have := typein_lt_typein_iff.mpr r
      rw [←h₀, h₁] at this
      apply typein_lt_typein_iff.mp
      assumption

def Pre.minelem (p: Pre) (h: Nonempty p.ty) : ∃x: p.ty, ∀y, ¬p.rel y x := by
  obtain ⟨x⟩ := h
  have ⟨x, _, spec⟩ := Relation.exists_min (P := fun _ => True) p.rel ⟨x, True.intro⟩
  exists x
  intro y r
  apply spec y r
  exact True.intro

def left_le_max' (a b: Ordinal) : a ≤ max a b := by

  classical
  induction a, b using ind₂ with | mk a b =>
  apply Nonempty.intro
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  intro a₀
  refine if h:∀b₀, typein b.rel b₀ < typein a.rel a₀ then ?_ else ?_
  apply Pre.maxType.inl
  assumption
  rw [Classical.not_forall] at h
  conv at h => { arg 1; intro; rw [←le_iff_not_lt] }
  have : ∃x, typein a.rel a₀ = typein b.rel x := by
    have ⟨x, le⟩ := h
    exact typein_surj b.rel (typein a.rel a₀) (lt_of_le_of_lt le (typein_lt _ _))
  apply Pre.maxType.mk a₀ (Classical.choose this)
  exact Classical.choose_spec this
  dsimp
  intro x y eq; dsimp at eq
  split at eq <;> split at eq <;> rename_i h₀ h₁
  exact Pre.maxType.inl.inj eq
  contradiction
  contradiction
  exact (Pre.maxType.mk.inj eq).left
  dsimp
  intro x y
  apply Iff.intro
  intro r
  dsimp
  split <;> split <;> rename_i h₀ h₁
  apply Pre.maxType.LT.inl
  assumption
  exfalso
  apply h₁
  intro b₀
  apply lt_trans
  apply h₀
  apply typein_lt_typein_iff.mpr
  assumption
  apply Pre.maxType.LT.mk_inl
  apply Pre.maxType.LT.mk
  assumption
  dsimp
  intro lt
  split at lt <;> split at lt <;> rename_i h₀ h₁
  cases lt
  assumption
  nomatch lt
  clear lt
  rw [Classical.not_forall] at h₀
  obtain ⟨b₀, le⟩ := h₀
  rw [←le_iff_not_lt] at le
  apply typein_lt_typein_iff.mp
  apply lt_of_le_of_lt
  assumption
  apply h₁
  cases lt
  assumption
  intro x y h
  replace h: y.LT (if _:_ then _ else _) := h
  apply Set.mem_range.mpr
  show ∃_, _ = if _:(∀_, _) then _ else _
  split at h
  cases h
  rename_i a₀ _ _ _
  exists a₀
  rw [dif_pos]
  rename_i a₀ b₀ _ _
  exists a₀
  rename_i h _
  rw [dif_neg]
  congr
  have : ∃ x, typein a.rel a₀ = typein b.rel x := ⟨_, h⟩
  have := h.symm.trans (Classical.choose_spec this)
  exact typein_inj _ this
  intro g
  have := g b₀
  rw [h] at this
  exact lt_irrefl this
  cases h
  rename_i a₀ b₀ h₀ _ h₁
  exists a₀
  rw [dif_neg]
  congr
  have : ∃ x, typein a.rel a₀ = typein b.rel x := ⟨_, h₀⟩
  apply typein_inj b.rel
  rw [←Classical.choose_spec this]
  symm; assumption
  rename_i h _
  intro g
  apply h
  intro y
  apply lt_trans
  apply g
  apply typein_lt_typein_iff.mpr
  assumption

def max_eq_left_iff (a b: Ordinal) : max a b = a ↔ b ≤ a := by
  apply Iff.intro
  intro h
  rw [←h, max_comm']
  apply left_le_max'
  induction a, b using ind₂ with | mk a b =>
  intro ⟨le⟩
  apply sound
  classical
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  intro x
  match x with
  | .inr b₀ h =>
    have := h (le b₀)
    rw [typein_congr_initial le (a := b₀)] at this
    exact (lt_irrefl this).elim
  | .inl a₀ h => assumption
  | .mk a₀ b₀ h => assumption
  intro a₀
  refine if h:a₀ ∈ Set.range le then ?_ else ?_
  apply Pre.maxType.mk a₀ (Classical.choose <| Set.mem_range.mp h)
  conv => { lhs; rw [Classical.choose_spec <| Set.mem_range.mp h] }
  rw [typein_congr_initial]
  apply Pre.maxType.inl a₀
  intro b₀
  apply lt_of_not_le
  intro g
  rw [Set.mem_range, not_exists] at h
  rw [←typein_congr_initial le] at g
  rcases lt_or_eq_of_le g with g | g
  replace g := typein_lt_typein_iff.mp g
  have ⟨b₁, eq⟩ := Set.mem_range.mp <| le.isInitial b₀ a₀ g
  subst eq
  exact h _ rfl
  have eq := typein_inj _ g
  subst eq
  exact h _ rfl
  · intro x
    dsimp
    cases x
    dsimp
    rw [dif_neg]
    · intro mem
      have ⟨b₀, eq⟩ := Set.mem_range.mp mem
      subst eq
      rename_i h
      have := h b₀
      rw [typein_congr_initial] at this
      exact lt_irrefl this
    dsimp
    contradiction
    dsimp
    rw [dif_pos]
    congr
    rename_i a₀ b₀ _
    have : ∃b', a₀ = le b' := by
      exists b₀
      apply typein_inj (r := a.rel)
      rw [typein_congr_initial]
      assumption
    apply le.inj
    show le _ = le _
    rw [←Classical.choose_spec this]
    apply typein_inj (r := a.rel)
    rw [typein_congr_initial]
    assumption
    apply Set.mem_range.mpr
    rename_i a₀ b₀ h
    exists b₀
    apply typein_inj (r := a.rel)
    rw [typein_congr_initial]
    assumption
  · intro x
    dsimp
    by_cases x ∈ Set.range le
    rw [dif_pos]
    assumption
    rw [dif_neg]
    assumption
  · intro x y
    cases x <;> cases y
    all_goals apply Iff.intro
    all_goals intro h
    any_goals
      dsimp only
      contradiction
    any_goals
      rename b.ty => b₀
      rename ∀ (a_1 : a.ty), typein a.rel a_1 < typein b.rel b₀ => h'
      have := lt_irrefl (cast (congrArg (fun _a => _a < typein b.rel b₀) (typein_congr_initial le)) (h' (le b₀)))
      contradiction
    cases h
    assumption
    apply Pre.maxType.LT.inl
    assumption
    dsimp at h
    rename_i h₀ a₀ b₀ eq
    have := lt_trans (h₀ b₀) (typein_lt_typein_iff.mpr h)
    rw [eq] at this
    have := lt_irrefl this
    contradiction
    rename_i b₀ _ _ _ _
    rename ∀ (a_1 : a.ty), typein a.rel a_1 < typein b.rel b₀ => h'
    have := lt_irrefl (cast (congrArg (fun _a => _a < typein b.rel b₀) (typein_congr_initial le)) (h' (le b₀)))
    contradiction
    dsimp
    rename_i a₀ b₀ h₀ a₁ h₁
    apply typein_lt_typein_iff.mp
    rw [h₀]
    apply h₁
    apply Pre.maxType.LT.mk_inl
    cases h
    assumption
    dsimp at h
    apply Pre.maxType.LT.mk
    assumption

instance : IsLinearMinMaxOrder Ordinal where
   min_iff_le_left := min_eq_left_iff
   min_iff_le_right := by
    intro a b
    rw [min_comm']
    exact min_eq_left_iff
   max_iff_le_left := by
    intro a b
    rw [max_comm']
    apply (max_eq_left_iff _ _).symm
   max_iff_le_right := by
    intro a b
    apply (max_eq_left_iff _ _).symm

def IsLimitOrdinal (o: Ordinal) := ∀x, x + 1 ≠ o

def lt_succ_self (a: Ordinal) : a < a + 1 := by
  cases a with | mk a =>
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩⟩
  exact .inl
  apply Sum.inl.inj
  intro a b
  apply Iff.intro
  exact Sum.Lex.inl
  intro h; cases h; assumption
  refine ⟨?_, ?_⟩
  unfold Pre.ofNat
  exact .inr ⟨0⟩
  intro x
  rw [Set.mem_range]
  apply Iff.intro
  intro h
  cases h
  contradiction
  refine ⟨_, rfl⟩
  intro ⟨a, eq⟩
  subst x
  apply Sum.Lex.sep

def lt_of_succ_le (a b: Ordinal) : a + 1 ≤ b -> a < b := by
  intro h
  apply lt_of_le_of_ne
  apply le_trans _ h
  apply le_add_left
  intro g
  rw [g] at h
  exact lt_irrefl <| lt_of_lt_of_le (lt_succ_self _) h

def zero_le (o: Ordinal) : 0 ≤ o := by
  induction o using ind with | mk o =>
  apply Nonempty.intro
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  exact fun x => x.down.elim0
  unfold Pre.ofNat
  apply empty_inj
  intro x; exact x.down.elim0
  intro x; exact x.down.elim0

def le_zero (o: Ordinal) : o ≤ 0 ↔ o = 0 := by
  apply flip Iff.intro
  · intro h
    rw [h]
  · cases o with | mk o =>
    intro ⟨h⟩
    apply sound
    have eqv := (empty_reliso_empty (fun a b: Empty => a.elim) (Pre.ofNat 0).lift.rel)
    replace h := h.congr .refl eqv.symm
    apply RelIso.trans _ eqv
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    intro x
    exact h x
    exact Empty.elim
    intro x
    exact (h x).elim
    exact Empty.rec
    intro x
    exact (h x).elim

def not_lt_zero (o: Ordinal) : ¬o < 0 := by
  cases o with | mk o =>
  intro ⟨h⟩
  have eqv := (empty_reliso_empty (fun a b: Empty => a.elim) (Pre.ofNat 0).lift.rel)
  replace h := h.congr .refl eqv.symm
  have ⟨_, _⟩ := h.exists_top
  contradiction

@[induction_eliminator]
def transfiniteInduction
  {motive: Ordinal -> Prop}
  (limit: ∀o, o.IsLimitOrdinal -> (∀x < o, motive x) -> motive o)
  (succ: ∀o, motive o -> motive (o+1)) (o: Ordinal):  motive o := by
  by_cases h:∃x, x + 1 = o
  have := succ _ (transfiniteInduction limit succ (Classical.choose h))
  rw [Classical.choose_spec h] at this
  exact this
  apply limit
  exact not_exists.mp h
  intro _ _
  apply transfiniteInduction limit succ
termination_by o
decreasing_by
  apply lt_of_succ_le
  rw [Classical.choose_spec h]
  assumption

def transfiniteInduction'
  {motive: Ordinal -> Prop}
  (zero: motive 0)
  (limit: ∀o, 0 < o -> o.IsLimitOrdinal -> (∀x < o, motive x) -> motive o)
  (succ: ∀o, motive o -> motive (o+1)) (o: Ordinal):  motive o := by
  induction o with
  | limit o olim ih =>
    by_cases h:o=0
    rw [h]; exact zero
    apply limit
    apply lt_of_le_of_ne
    apply zero_le
    symm; assumption
    assumption
    assumption
  | succ => apply succ; assumption

instance : Bot Ordinal := ⟨0⟩

instance : LawfulBot Ordinal where
  bot_le := zero_le

open Classical in
noncomputable instance : InfSet Ordinal where
  sInf s := if h:s.Nonempty then s.min (· < ·) h else ⊥

open Classical in
noncomputable instance : SupSet Ordinal where
  sSup s := if h:s.BoundedAbove then s.upperBounds.min (· < ·) h else ⊥

def sSup_eq_sInf_upperbounds (s: Set Ordinal) (h: s.BoundedAbove) : sSup s = sInf s.upperBounds := by
  simp [sSup, sInf]
  unfold Set.BoundedAbove at *
  rw [dif_pos h]

def sInf_le (s: Set Ordinal) : ∀x ∈ s, sInf s ≤ x := by
  intro x mem
  dsimp [sInf]
  rw [dif_pos ⟨_, mem⟩]
  apply le_of_not_lt
  apply Set.not_lt_min
  assumption

def le_sSup (s: Set Ordinal) (h: s.BoundedAbove) : ∀x ∈ s, x ≤ sSup s := by
  intro x mem
  dsimp [sSup]
  rw [dif_pos h]
  have := Set.min_mem (· < (·: Ordinal)) h
  rw [Set.mem_upperBounds] at this
  apply this
  assumption

def sInf_le' (s: Set Ordinal) (k: Ordinal) : (∀x ∈ s, x ≤ k) -> sInf s ≤ k := by
  intro h
  simp [sInf]
  split
  rename_i g
  obtain ⟨x, mem⟩ := g
  apply flip le_trans
  apply h
  assumption
  apply le_of_not_lt
  apply Set.not_lt_min
  assumption
  apply bot_le

def le_sInf (s: Set Ordinal) (h: s.Nonempty) (k: Ordinal) : (∀x ∈ s, k ≤ x) -> k ≤ sInf s := by
  intro g
  simp [sInf]
  rw [dif_pos h]
  apply g
  apply Set.min_mem

def sSup_empty : sSup ∅ = (0: Ordinal) := by
  have zero_in_upper_bounds: (0: Ordinal) ∈ Set.upperBounds ∅ := fun x h => (Set.not_mem_empty h).elim
  have empty_bounded : (∅: Set Ordinal).BoundedAbove := ⟨0, zero_in_upper_bounds⟩
  simp [sSup]
  rw [dif_pos empty_bounded]
  apply le_antisymm
  apply le_of_not_lt
  apply Set.not_lt_min
  assumption
  apply zero_le

def le_sSup' (s: Set Ordinal) (h: s.BoundedAbove) : (∀x ∈ s.upperBounds, k ≤ x) -> k ≤ sSup s := by
  intro g
  rw [sSup_eq_sInf_upperbounds]
  apply le_sInf <;> assumption
  assumption

def sSup_le (s: Set Ordinal) (h: s.BoundedAbove) (k: Ordinal) : (∀x ∈ s, x ≤ k) -> sSup s ≤ k := by
  intro g
  simp [sSup]
  rw [dif_pos h]
  obtain ⟨x, mem⟩ := h
  apply le_of_not_lt
  apply Set.not_lt_min
  rw [Set.mem_upperBounds]
  apply g

def ofNat_le_ofNat (n m: Nat) : Ordinal.ofNat n ≤ Ordinal.ofNat m ↔ n ≤ m := by
  apply Iff.intro
  intro ⟨h⟩
  have := Fintype.existsEmbedding_iff_card_le.mp ⟨h.toEmbedding⟩
  rw [Fin.card_eq, Fin.card_eq] at this
  assumption
  intro h
  refine ⟨Fin.relEmbedFin h, ?_⟩
  intro a b g
  replace g : b < a.castLE h := g
  apply Set.mem_range.mpr
  refine ⟨⟨?_, ?_⟩, ?_⟩
  exact b.val
  apply Nat.lt_trans
  exact g
  exact a.isLt
  rfl

def ofNat_lt_ofNat (n m: Nat) : Ordinal.ofNat n < Ordinal.ofNat m ↔ n < m := by
  apply lt_iff_of_le_iff
  apply ofNat_le_ofNat

def natCast_le_natCast (n m: Nat) : (n: Ordinal) ≤ m ↔ n ≤ m := by
  apply Iff.trans _ (ofNat_le_ofNat n m)
  apply Iff.intro
  intro ⟨h⟩
  apply Nonempty.intro
  apply h.congr
  apply ULift.relIso
  apply ULift.relIso
  intro ⟨h⟩
  apply Nonempty.intro
  apply h.congr
  apply (ULift.relIso _).symm
  apply (ULift.relIso _).symm

def natCast_lt_natCast (n m: Nat) : (n: Ordinal) < m ↔ n < m := by
  apply lt_iff_of_le_iff
  apply natCast_le_natCast

def omega := type (· < (·: Nat))
def omega' := omega.lift

scoped notation "ω" => omega'

def lt_omega (x: Ordinal) : x < ω -> ∃n: Nat, x = n := by
  cases x with | mk X =>
  intro ⟨h⟩
  replace h := h.congr .refl (ULift.relIso _)
  dsimp at h
  obtain ⟨top, spec⟩ := h.exists_top
  exists top
  apply sound
  apply flip RelIso.trans
  symm; unfold Pre.lift; dsimp
  apply (ULift.relIso _)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  intro x
  refine ⟨h x, ?_⟩
  apply (spec _).mpr
  apply Set.mem_range'
  intro n
  exact Classical.choose <| Set.mem_range.mp <| (spec n.val).mp n.isLt
  intro x
  dsimp
  symm; apply h.inj
  have : ∃ a', h x = h a' := Set.mem_range.mp ((spec (h x)).mp <| (spec (h x)).mpr Set.mem_range')
  apply Classical.choose_spec this
  intro x
  dsimp
  apply Fin.val_inj.mp
  dsimp
  have := Set.mem_range.mp ((spec x.val).mp x.isLt)
  symm; apply Classical.choose_spec this
  dsimp
  exact h.resp_rel

def zero_limit : IsLimitOrdinal 0 := by
  intro x h
  cases x with | mk x =>
  rw [one_eq, zero_eq] at h
  replace ⟨h⟩ := Quotient.exact h
  have := h (.inr default)
  contradiction

def omega_limit : IsLimitOrdinal ω := by
  intro x h
  cases x with | mk x =>
  rw [one_eq] at h
  replace ⟨h⟩ := Quotient.exact h
  unfold Pre.lift at h
  dsimp at h
  replace h := h.trans (ULift.relIso _)
  generalize hx:h (.inr default) = x
  match h₀:h.symm (x+1) with
  | .inr _ =>
    replace h₀: h.symm (x + 1) = (Sum.inr default) := h₀
    rw [←h₀] at hx
    rw [h.symm_coe] at hx
    exact Nat.succ_ne_self _ hx
  | .inl _ =>
    have : (Pre.add _ _).rel (h.symm x) (h.symm (x + 1)) := h.symm.resp_rel.mp (Nat.lt_succ_self x)
    rw [h₀, ←hx] at this
    rw [h.coe_symm] at this
    contradiction

def OfNat_eq_cast (n: Nat) : OfNat.ofNat n = (n: Ordinal) := rfl

inductive Pre.succRel (r: α -> α -> Prop) : Option α -> Option α -> Prop where
| none x : succRel r (.some x) .none
| some x y : r x y -> succRel r (.some x) (.some y)

instance [Relation.IsTrans r] : Relation.IsTrans (Pre.succRel r) where
  trans := by
    intro a b c ab bc
    cases ab <;> cases bc
    apply Pre.succRel.none
    apply Pre.succRel.some
    apply Relation.trans <;> assumption
instance [Relation.IsTrichotomous r] : Relation.IsTrichotomous (Pre.succRel r) where
  tri := by
    intro a b
    cases a <;> cases b
    right; left; rfl
    right; right; apply Pre.succRel.none
    left; apply Pre.succRel.none
    rename_i a b
    rcases Relation.trichotomous r a b with ab | eq | ba
    left; apply Pre.succRel.some; assumption
    right; left; congr
    right; right; apply Pre.succRel.some; assumption
instance [Relation.IsWellFounded r] : Relation.IsWellFounded (Pre.succRel r) where
  wf := by
    suffices ∀x, Acc (Pre.succRel r) (.some x) by
      apply WellFounded.intro
      intro x
      apply Acc.intro
      intro y r
      cases r
      apply this
      apply this
    intro x
    induction x using Relation.wfInduction r with | h x ih =>
    apply Acc.intro
    intro y r
    cases r
    apply ih
    assumption

def Pre.succ (p: Pre) : Pre where
  ty := Option p.ty
  rel := Pre.succRel p.rel

def Pre.succ.spec (a b: Pre) (h: a.rel ≃r b.rel) : a.succ.rel ≃r b.succ.rel where
  toEquiv := Option.congrEquiv h.toEquiv
  resp_rel := by
    intro x y
    apply Iff.intro
    intro r
    cases r
    apply Pre.succRel.none
    apply Pre.succRel.some
    apply h.resp_rel.mp
    assumption
    intro r
    cases x <;> cases y <;>
    cases r
    apply Pre.succRel.none
    apply Pre.succRel.some
    apply h.resp_rel.mpr
    assumption

def succ : Ordinal -> Ordinal := by
  apply Quotient.lift (fun x => ⟦x.succ⟧)
  intro a b ⟨ab⟩
  apply sound
  exact Pre.succ.spec _ _ ab

def add_one_eq_succ (a: Ordinal) : a + 1 = a.succ := by
  cases a with | mk A =>
  symm
  apply sound
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  intro x
  match x with
  | .some x => exact .inl x
  | .none => exact .inr default
  intro x
  match x with
  | .inl x => exact .some x
  | .inr _ => exact .none
  intro x
  cases x <;> rfl
  intro x
  cases x
  rfl
  dsimp; congr
  apply Subsingleton.allEq _ _
  intro x y
  cases x <;> cases y
  all_goals apply Iff.intro
  all_goals intro h
  any_goals contradiction
  apply Sum.Lex.sep
  apply Pre.succRel.none
  cases h
  apply Sum.Lex.inl; assumption
  cases h
  apply Pre.succRel.some
  assumption

def succ_le_of_lt (a b: Ordinal) : a < b -> a + 1 ≤ b := by
  rw [add_one_eq_succ]
  induction a, b using ind₂ with | mk A B =>
  intro ⟨h⟩
  have ⟨top, spec⟩ := h.exists_top
  have hx_lt_top : ∀x, B.rel (h x) top := by
    intro x
    exact (spec (h x)).mpr (Set.mem_range')
  have hx_ne_top : ∀x, h x ≠ top := by
    intro x eq
    exact Relation.irrefl (eq ▸ hx_lt_top x)
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  intro x
  match x with
  | .some x => exact h x
  | .none => exact top
  intro x y eq
  cases x <;> cases y <;> dsimp at eq
  rfl
  have := hx_ne_top _ eq.symm
  contradiction
  have := hx_ne_top _ eq
  contradiction
  rw [h.inj eq]
  intro a₀ a₁
  · apply Iff.intro
    all_goals intro g; cases a₀ <;> cases a₁
    any_goals contradiction
    apply hx_lt_top
    cases g
    apply h.resp_rel.mp
    assumption
    have := Relation.irrefl g
    contradiction
    have := Relation.asymm g (hx_lt_top _)
    contradiction
    apply Pre.succRel.none
    apply Pre.succRel.some
    apply h.resp_rel.mpr
    assumption
  intro a b r
  cases a
  replace r : B.rel b top := r
  have ⟨a, eq⟩ := Set.mem_range.mp <| (spec _).mp r
  subst eq
  apply Set.mem_range.mpr
  exists .some a
  rename_i a
  replace r : B.rel b (h a) := r
  replace r : B.rel b top := Relation.trans r (hx_lt_top _)
  have ⟨a, eq⟩ := Set.mem_range.mp <| (spec _).mp r
  subst eq
  apply Set.mem_range.mpr
  exists .some a

end Ordinal
