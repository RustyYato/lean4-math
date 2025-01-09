import Math.Relation.Basic
import Math.Relation.RelIso
import Math.Tactics.PPWithUniv
import Math.Relation.Segments
import Math.Order.Linear
import Math.AxiomBlame
import Math.Data.Quotient.Basic

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

instance : IsEmpty (Pre.ofNat 0).ty := inferInstanceAs (IsEmpty (Fin 0))
instance (p: Pre) [IsEmpty p.ty] : IsEmpty p.lift.ty := inferInstanceAs (IsEmpty (ULift p.ty))

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

def left_le_add (a b: Ordinal) : a ≤ a + b := by
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

def right_le_add (a b: Ordinal) : b ≤ a + b := by
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

end Ordinal
