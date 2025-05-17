import Math.Relation.RelIso
import Math.Tactics.PPWithUniv
import Math.Relation.Segments
import Math.Order.Defs
import Math.Data.Fin.Pairing
import Math.Order.Lattice.ConditionallyComplete
import Math.Data.Setoid.Basic

universe u v w

variable {α β γ δ: Type _}
  (rel: α -> α -> Prop)
  (relα: α -> α -> Prop) (relβ: β -> β -> Prop)
  (relγ: γ -> γ -> Prop) (relδ: δ -> δ -> Prop)
  {r: α -> α -> Prop} {s: β -> β -> Prop}
  {t: γ -> γ -> Prop} {u: δ -> δ -> Prop}
  [Relation.IsWellOrder rel]
  [Relation.IsWellOrder relα] [Relation.IsWellOrder relβ]
  [Relation.IsWellOrder relγ] [Relation.IsWellOrder relδ]
  [Relation.IsWellOrder r] [Relation.IsWellOrder s]
  [Relation.IsWellOrder t] [Relation.IsWellOrder u]

namespace Ordinal

section Defs

@[pp_with_univ]
structure Pre: Type (u + 1) where
  ty: Type u
  rel: Relation ty
  well_order: Relation.IsWellOrder rel := by infer_instance

instance (p: Pre) : Relation.IsWellOrder p.rel := p.well_order

instance (p: Pre) : Relation.IsWellOrder (fun x y => p.rel x y) := p.well_order

instance pre_setoid : Setoid Pre where
  r a b := Nonempty (a.rel ≃r b.rel)
  iseqv := {
    refl _ := ⟨RelIso.refl⟩
    symm | ⟨h⟩ => ⟨h.symm⟩
    trans | ⟨h⟩, ⟨g⟩ => ⟨h.trans g⟩
  }

@[pp_with_univ]
def _root_.Ordinal := Quotient pre_setoid

def ofPre : Pre -> Ordinal := Quotient.mk _
def type {α: Type u} (rel: α -> α -> Prop) [Relation.IsWellOrder rel] : Ordinal := ofPre (Pre.mk _ rel)

@[cases_eliminator]
def ind {motive : Ordinal -> Prop} (type: ∀(α: Type u) (rel: α -> α -> Prop) [Relation.IsWellOrder rel], motive (type rel)) (o: Ordinal) : motive o := by
  induction o using Quotient.ind with | _ o =>
  apply type

def sound {α β: Type u} (relα: α -> α -> Prop) (relβ: β -> β -> Prop) [hrelα: Relation.IsWellOrder relα] [hrelβ: Relation.IsWellOrder relβ] :
  relα ≃r relβ -> type relα = type relβ := by intro h; exact Quotient.sound ⟨h⟩

def sound' {α β: Type u} (relα: α -> α -> Prop) (relβ: β -> β -> Prop) (hrelα: Relation.IsWellOrder relα := by infer_instance) (hrelβ: Relation.IsWellOrder relβ := by infer_instance) :
  relα ≃r relβ -> type relα = type relβ := by intro h; exact Quotient.sound ⟨h⟩

def lift {A: Type w} (f: ∀(α: Type u) (relα: α -> α -> Prop) [Relation.IsWellOrder relα], A) (hf: ∀(α β: Type u) (relα: α -> α -> Prop) (relβ: β -> β -> Prop) [Relation.IsWellOrder relα] [Relation.IsWellOrder relβ], relα ≃r relβ -> f α relα = f β relβ) : Ordinal -> A := by
  refine Quotient.lift (fun p => f p.ty p.rel) ?_
  intro a b ⟨h⟩; apply hf
  assumption

def lift₂ {A: Type w} (f: ∀(α: Type u) (β: Type v) (relα: α -> α -> Prop) (relβ: β -> β -> Prop) [Relation.IsWellOrder relα] [Relation.IsWellOrder relβ], A)
  (hf: ∀(α β γ δ)
    (relα: α -> α -> Prop) (relβ: β -> β -> Prop)
    (relγ: γ -> γ -> Prop) (relδ: δ -> δ -> Prop)
    [Relation.IsWellOrder relα] [Relation.IsWellOrder relβ]
    [Relation.IsWellOrder relγ] [Relation.IsWellOrder relδ],
    relα ≃r relγ ->
    relβ ≃r relδ -> f α β relα relβ = f γ δ relγ relδ) : Ordinal -> Ordinal -> A := by
  refine Quotient.lift₂ (fun p q => f _ _ p.rel q.rel) ?_
  intro a b c d ⟨h⟩ ⟨g⟩; apply hf
  assumption
  assumption

def exact : type r = type s -> Nonempty (r ≃r s) := Quotient.exact

def exists_rep (o: Ordinal) : ∃(α: Type _) (rel: α -> α -> Prop) (_hrel: Relation.IsWellOrder rel), o = type rel := by
  obtain ⟨p, eq⟩  := Quotient.exists_rep o
  rw [←eq]
  exists p.ty
  exists p.rel
  exists p.well_order

attribute [irreducible] Ordinal

def rel_ulift : Relation (ULift α) := fun a b => rel a.down b.down
def rel_ulift_eqv : rel_ulift rel ≃r rel where
  toEquiv := Equiv.ulift _
  resp_rel := Iff.rfl
def rel_ulift_hom : rel_ulift rel ↪r rel := (rel_ulift_eqv rel).toRelEmbedding

instance : Relation.IsWellOrder (rel_ulift rel) := (rel_ulift_hom rel).lift_wo

@[pp_with_univ]
def ulift : Ordinal.{v} -> Ordinal.{max u v} := by
  refine lift (fun α relα _ => Ordinal.type (rel_ulift relα)) ?_
  · intro α β relα relβ _ _ h
    dsimp
    apply sound
    exact {
      Equiv.congrULift h.toEquiv with
      resp_rel := h.resp_rel
    }

instance : LE Ordinal where
  le := by
    refine lift₂ (fun _ _ relα relβ _ _ => Nonempty (relα ≼i relβ)) ?_
    intro A B C D relA relB relC relD _ _ _ _ ac bd
    dsimp
    ext
    apply Iff.intro
    intro ⟨h⟩; refine ⟨?_⟩
    apply h.congr
    assumption
    assumption
    intro ⟨h⟩; refine ⟨?_⟩
    apply h.congr
    symm; assumption
    symm; assumption

instance : LT Ordinal where
  lt := by
    refine lift₂ (fun _ _ relα relβ _ _ => Nonempty (relα ≺i relβ)) ?_
    intro A B C D relA relB relC relD _ _ _ _ ac bd
    dsimp
    ext
    apply Iff.intro
    intro ⟨h⟩; refine ⟨?_⟩
    apply h.congr
    assumption
    assumption
    intro ⟨h⟩; refine ⟨?_⟩
    apply h.congr
    symm; assumption
    symm; assumption

instance : IsPartialOrder Ordinal where
  le_refl a := by
    cases a with | _ α rel =>
    exact ⟨InitialSegment.refl _⟩
  le_trans {a b c} h g := by
    cases a with | _ a rela =>
    cases b with | _ b relb =>
    cases c with | _ c relc =>
    obtain ⟨h⟩ := h
    obtain ⟨g⟩ := g
    dsimp at h g
    exact ⟨h.trans g⟩
  le_antisymm {a b} h g := by
    cases a with | _ a rela =>
    cases b with | _ b relb =>
    obtain ⟨h⟩ := h
    obtain ⟨g⟩ := g
    dsimp at h g
    apply sound
    exact InitialSegment.antisymm h g
  lt_iff_le_and_not_le {a b} := by
    cases a with | _ a rela =>
    cases b with | _ b relb =>
    apply Iff.intro
    · intro ⟨h⟩
      dsimp at h
      apply And.intro
      exact ⟨h⟩
      intro ⟨g⟩
      dsimp at g
      exact PrincipalSegment.irrefl (PrincipalSegment.lt_of_lt_of_le h g)
    · intro ⟨⟨h⟩, g⟩
      dsimp at h
      rcases Or.symm (InitialSegment.eqv_or_principal h) with ⟨top, htop⟩ | hsurj
      · refine ⟨{ h with exists_top := ?_ }⟩
        exists top
      · exfalso; apply g
        have ⟨eqv, heqv⟩ := Equiv.ofBij ⟨h.inj, hsurj⟩
        have iso : rela ≃r relb := {
          eqv with
          resp_rel := by
            simp
            rw [heqv]
            exact h.resp_rel
        }
        apply InitialSegment.collapse
        dsimp
        exact ⟨iso.symm.toEmbedding⟩

def add : Ordinal -> Ordinal -> Ordinal := by
  refine lift₂ (fun a b rela relb _ _ => type (Sum.Lex rela relb)) ?_
  intro a b c d rela relb relc reld _ _ _ _ ac bd
  apply sound
  exact RelIso.congrSumLex rela relb relc reld ac bd

def mul : Ordinal -> Ordinal -> Ordinal := by
  refine lift₂ (fun a b rela relb _ _ => type (Prod.Lex rela relb)) ?_
  intro a b c d rela relb relc reld _ _ _ _ ac bd
  apply sound
  exact RelIso.congrProdLex rela relb relc reld ac bd

instance : Add Ordinal where
  add := add
instance : Mul Ordinal where
  mul := mul

def rel_rank (top: α) : Relation { x: α // rel x top } := fun a b => rel a b
def rel_rank_emb (top: α) : rel_rank rel top ↪r rel where
  toFun x := x.val
  inj' := Subtype.val_inj
  resp_rel := Iff.rfl
def rel_rank_princ_top (top: α) : (rel_rank_emb rel top).IsPrincipalTop top := by
  intro x
  apply Iff.intro
  intro h
  exists ⟨x, h⟩
  rintro ⟨x, rfl⟩
  exact x.property
def rel_rank_hom (top: α) : rel_rank rel top ≺i rel where
  toRelEmbedding := rel_rank_emb rel top
  exists_top := by exists top; apply rel_rank_princ_top

instance : Relation.IsWellOrder (rel_rank rel top) :=
  (rel_rank_hom rel top).toRelEmbedding.lift_wo

def rank (a: α) := Ordinal.type (rel_rank rel a)
def rank' (rel: α -> α -> Prop) (h: Relation.IsWellOrder rel) (a: α) := rank rel a

def rank_surj : ∀o < type rel, ∃a, o = rank rel a := by
  intro o ho
  cases o with | _ β relβ =>
  obtain ⟨ho⟩ := ho
  dsimp at ho
  have ⟨top, htop⟩ := ho.exists_top
  have f : ∀a: { x: α // rel x top }, ∃b: β, a.val = ho b := by intro x; exact (htop x).mp x.property
  replace ⟨f, hf⟩ := Classical.axiomOfChoice f
  unfold RelEmbedding.IsPrincipalTop at htop
  exists top
  apply sound
  exact {
    toFun b := {
      val := ho b
      property := by
        apply (htop (ho b)).mpr
        apply Set.mem_range'
    }
    invFun := f
    leftInv b := by
      dsimp
      have := hf ⟨ho b, (htop (ho b)).mpr Set.mem_range'⟩
      simp at this; erw [ho.inj.eq_iff] at this
      symm; assumption
    rightInv a := by dsimp; congr; symm; apply hf
    resp_rel := ho.resp_rel
  }

def rank_lt_type (a: α) : rank r a < type r := ⟨rel_rank_hom r a⟩

def rel_rank_lt_rel_rank_init (init: r ≼i s) (a: α) (b: β) (h: s (init a) b) : rel_rank r a ≺i rel_rank s b where
  toFun x := {
    val := init x.val
    property := trans (init.resp_rel.mp x.property) h
  }
  inj' := by
    intro ⟨x, xLt⟩ ⟨y, yLt⟩ h
    simp at h
    congr; exact init.inj h
  resp_rel := init.resp_rel
  exists_top := by
    exists ⟨init a, h⟩
    intro ⟨x, hx⟩
    dsimp
    apply Iff.intro
    · intro g
      obtain ⟨x, rfl⟩ := init.isInitial _ _ g
      refine ⟨⟨x, ?_⟩, rfl⟩
      exact init.resp_rel.mpr g
    · intro g
      show s x (init a)
      obtain ⟨⟨_, hx'⟩, eq⟩ := g
      cases eq
      apply init.resp_rel.mp
      assumption

def rel_rank_rel_rank (a b: α) (h: r b a) : rel_rank (rel_rank r a) ⟨b, h⟩ ≃r rel_rank r b where
  toFun x := {
    val := x.val.val
    property := x.property
  }
  invFun x := {
    val := {
      val := x.val
      property := trans x.property h
    }
    property := x.property
  }
  leftInv _ := rfl
  rightInv _ := rfl
  resp_rel := Iff.rfl

def rank_lt_rank_init_iff (init: r ≼i s) (a: α) (b: β) : rank r a < rank s b ↔ s (init a) b := by
  symm; apply Iff.intro
  · intro h
    exact ⟨rel_rank_lt_rel_rank_init init a b h⟩
  · intro ⟨h⟩
    dsimp at h

    let r₀ := h.trans (rel_rank_hom s b)
    let r₁ := (rel_rank_hom r a).lt_of_lt_of_le init
    have eq : r₁ = r₀ := Subsingleton.allEq _ _
    have princ_top: r₁.IsPrincipalTop (init a) := by
      apply PrincipalSegment.top_of_lt_of_lt_of_le
      apply rel_rank_princ_top
    rw [eq] at princ_top
    have ⟨top, htop⟩ := h.exists_top
    have top' : r₀.IsPrincipalTop top := by
      apply PrincipalSegment.top_of_lt_of_lt_of_le
      assumption
    rw [PrincipalSegment.top_unique' _ _ _ princ_top top']
    exact top.property

def rank_lt_rank_iff {a b: α} : rank r a < rank r b ↔ r a b := rank_lt_rank_init_iff (InitialSegment.refl _) _ _

def rank_congr (init: r ≼i s) (top: α) : rank s (init top) = rank r top := by
  have (x: { b: β // s b (init top) }) : x.val ∈ Set.range init := init.isInitial top x.val x.property
  replace := Classical.axiomOfChoice this
  obtain ⟨f, hf⟩ := this
  apply sound
  refine RelIso.symm {
    toFun x := {
      val := init x
      property := by
        apply init.resp_rel.mp
        exact x.property
    }
    invFun x := {
      val := f x
      property := by
        apply init.resp_rel.mpr
        show s (init _) (init _)
        rw [←hf]
        exact x.property
    }
    leftInv x := by
      simp; congr
      apply init.inj
      rw [←hf]
    rightInv x := by
      simp; congr; rw [←hf]
    resp_rel := init.resp_rel
  }

def rank_rel_rank (a b: α) (h: r b a) : rank (rel_rank r a) ⟨b, h⟩ = rank r b := by
  apply sound
  apply rel_rank_rel_rank

def rank_inj_initial (init: r ≼i s) (a: α) (b: β) : rank r a = rank s b -> b = init a := by
  intro h
  apply Relation.eq_of_not_lt_or_gt s
  intro g
  obtain ⟨b, rfl⟩ := init.isInitial _ _ g
  simp at *
  rw [←rank_lt_rank_init_iff init, rank_congr, h, rank_congr] at g
  exact lt_irrefl g
  intro g
  rw [←rank_lt_rank_init_iff init, h] at g
  exact lt_irrefl g

def rank_inj : Function.Injective (rank r) := by intro x y h; apply rank_inj_initial (InitialSegment.refl r) _ _ h.symm

instance : @Relation.IsWellFounded Ordinal (· < ·) where
  wf := by
    apply WellFounded.intro
    intro a
    apply Acc.intro
    intro b r
    cases a with | _ _ rel =>
    have ⟨a₀, eq⟩ := rank_surj rel b r
    subst b
    clear r
    induction a₀ using (Relation.wellFounded rel).induction with
    | h a₀ ih =>
    apply Acc.intro
    intro c r
    have ⟨c₀, eq⟩ := rank_surj _ _ (lt_trans r (rank_lt_type _))
    subst eq
    apply ih
    apply rank_lt_rank_iff.mp r

instance : WellFoundedRelation Ordinal where
  rel a b := a < b
  wf := Relation.wellFounded _

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
  cases o with | _ _ rel =>
  have ⟨a, eq⟩ := rank_surj _ a ao
  subst eq
  have ⟨b, eq⟩ := rank_surj _ b bo
  subst eq
  rcases Relation.connected rel a b with ab | eq | ba
  left; apply le_of_lt; apply rank_lt_rank_iff.mpr; assumption
  left; rw [eq]
  right; apply le_of_lt; apply rank_lt_rank_iff.mpr; assumption

def rel_add_of_left : r ≼i Sum.Lex r s where
  toFun := Sum.inl
  inj' _ _ := Sum.inl.inj
  resp_rel {_ _} := by simp
  isInitial := by
    intro a b h
    cases h
    apply Set.mem_range'

def apply_rel_add_of_left (x: α) : rel_add_of_left (r := r) (s := s) x = Sum.inl x := rfl

def le_add_left (a b: Ordinal) : a ≤ a + b := by
  cases a with | _ _ a =>
  cases b with | _ _ b =>
  apply Nonempty.intro
  apply rel_add_of_left

def le_add_right (a b: Ordinal) : b ≤ a + b := by
  cases a with | _ _ a =>
  cases b with | _ _ b =>
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

instance : @Relation.IsTotal Ordinal (· ≤ ·) where
  total a b := by
    apply le_total_of_le (a + b)
    apply le_add_left
    apply le_add_right

instance : IsLinearOrder Ordinal := inferInstance
instance : @Relation.IsWellOrder Ordinal (· < ·) := inferInstance
instance : @Relation.IsConnected Ordinal (· < ·) := inferInstance

def rank_le_rank_iff {a b: α} : rank r a ≤ rank r b ↔ ¬r b a := by
  rw [←not_lt]
  apply Iff.not_iff_not
  apply rank_lt_rank_iff

def ulift_le_ulift (a b: Ordinal.{u}) : ulift.{v} a ≤ ulift.{v} b ↔ a ≤ b := by
  cases a with | _ _ a =>
  cases b with | _ _ b =>
  apply Iff.intro
  intro ⟨h⟩
  refine ⟨?_⟩
  apply h.congr
  apply rel_ulift_eqv
  apply rel_ulift_eqv
  intro ⟨h⟩
  refine ⟨?_⟩
  apply h.congr
  symm; apply rel_ulift_eqv
  symm; apply rel_ulift_eqv

def ulift_lt_ulift (a b: Ordinal.{u}) : ulift.{v} a < ulift.{v} b ↔ a < b := by
  cases a with | _ _ a =>
  cases b with | _ _ b =>
  apply Iff.intro
  intro ⟨h⟩
  refine ⟨?_⟩
  apply h.congr
  apply rel_ulift_eqv
  apply rel_ulift_eqv
  intro ⟨h⟩
  refine ⟨?_⟩
  apply h.congr
  symm; apply rel_ulift_eqv
  symm; apply rel_ulift_eqv

@[ext]
def ext (a b: Ordinal): (∀x, x < a ↔ x < b) -> a = b := by
  intro h
  rcases lt_trichotomy a b with ab | eq | ba
  have := lt_irrefl <| (h a).mpr ab
  contradiction
  assumption
  have := lt_irrefl <| (h b).mp ba
  contradiction

def rank_eq_ulift (a: Ordinal.{u}) : rank (· < ·) a = ulift.{u + 1, u} a := by
  cases a with | _ A rel =>
  have (x: { o: Ordinal // o < type rel }) := rank_surj rel x.val x.property
  replace this := Classical.axiomOfChoice this
  obtain ⟨f, hf⟩ := this
  simp at hf
  apply sound
  simp
  apply RelIso.trans _ (rel_ulift_eqv _).symm
  exact RelIso.symm {
    toFun b := ⟨rank rel b, rank_lt_type _⟩
    invFun := f
    leftInv x := by
      simp
      apply rank_inj (r := rel)
      symm; apply hf
    rightInv y := by
      simp; congr
      symm; apply hf
    resp_rel := by
      intro a b
      apply rank_lt_rank_iff.symm
  }

end Defs

section Lattice

section Min

-- the minimum of two relations is the relation on pairs of elements which
-- are in the same position as each other in their respective orders
-- since this puts elements in 1-1 correspondence, there can't be elements
-- than the smaller of the two relations
def minType := { x: α × β // rank relα x.fst = rank relβ x.snd }

def rel_min : Relation (minType relα relβ) := fun a b => relα a.val.fst b.val.fst
def rel_min' : Relation (minType relα relβ) := fun a b => relβ a.val.snd b.val.snd

def rel_min_eq_rel_min' : rel_min relα relβ = rel_min' relα relβ := by
  ext ⟨⟨x₀, x₁⟩, hx⟩ ⟨⟨y₀, y₁⟩, hy⟩
  unfold rel_min rel_min'
  simp
  simp at hx hy
  apply Iff.intro
  · intro h
    rcases Relation.connected relβ x₁ y₁ with hβ | hβ | hβ
    assumption
    · subst y₁
      rw [←hx] at hy
      cases rank_inj hy
      have := Relation.irrefl h
      contradiction
    · rw [←rank_lt_rank_iff (r := relβ)] at hβ
      rw [←hx, ←hy] at hβ
      rw [rank_lt_rank_iff] at hβ
      have := Relation.asymm h hβ
      contradiction
  · intro h
    rcases Relation.connected relα x₀ y₀ with hα | hα | hα
    assumption
    · subst y₀
      rw [hx] at hy
      cases rank_inj hy
      have := Relation.irrefl h
      contradiction
    · rw [←rank_lt_rank_iff (r := relα)] at hα
      rw [hx, hy] at hα
      rw [rank_lt_rank_iff] at hα
      have := Relation.asymm h hα
      contradiction

def rel_min_comm : rel_min relα relβ ≃r rel_min relβ relα where
  toEquiv := Equiv.congrSubtype (Equiv.commProd _ _) <| by intro (a, b); apply Eq.comm
  resp_rel := by
    intro x y
    show rel_min _ _ x y ↔ rel_min' _ _ x y
    rw [rel_min_eq_rel_min']

def rel_min_hom_left : rel_min relα relβ ≼i relα where
  toFun x := x.val.1
  inj' := by
    intro ⟨⟨x₀, x₁⟩, hx⟩ ⟨⟨y₀, y₁⟩, hy⟩ h
    simp at h hx hy
    subst h
    suffices x₁ = y₁ by subst this; rfl
    rwa [hx, rank_inj.eq_iff] at hy
  resp_rel := Iff.rfl
  isInitial := by
    intro ⟨⟨x₀, x₁⟩, hx⟩ a
    show relα a x₀ -> _
    intro h
    suffices ∃b, rank relα a = rank relβ b by
      obtain ⟨b, eq⟩ := this
      exists ⟨⟨_, _⟩, eq⟩
    have ⟨ltα⟩ := rank_lt_type (r := relα) x₀
    have ⟨ltβ⟩ := rank_lt_type (r := relβ) x₁
    replace ⟨hx⟩ := exact hx
    let ha := rel_rank_lt_rel_rank_init (InitialSegment.refl relα) a x₀ h
    let b := hx ⟨a, h⟩
    have htop := PrincipalSegment.top_of_lt_of_lt_of_le ha (InitialSegment.ofRelIso hx) ⟨_, h⟩ <| by
      intro ⟨x, hx⟩
      simp
      show relα x a ↔ _
      apply Iff.intro
      · intro x_lt_a
        refine ⟨_, x_lt_a, ?_⟩
        rfl
      · intro ⟨_, _, rfl⟩
        assumption
    exists b
    rw [←rank_rel_rank (r := relα) _ _ h, ←rank_rel_rank (r := relβ)]
    symm; apply rank_congr (InitialSegment.ofRelIso hx)

def rel_min_hom_right : rel_min relα relβ ≼i relβ := by
  apply InitialSegment.congr
  apply rel_min_comm
  rfl
  apply rel_min_hom_left

instance [Relation.IsWellOrder relα] [Relation.IsWellOrder relβ] : Relation.IsWellOrder (rel_min relα relβ) :=
  (rel_min_hom_left _ _).toRelEmbedding.lift_wo

def min : Ordinal -> Ordinal -> Ordinal := by
  refine lift₂ (fun _ _ rela relb _ _ => type (rel_min rela relb)) ?_
  intro A B C D rela relb relc reld _ _ _ _ ac bd
  simp; apply sound
  refine {
      Equiv.congrSubtype (Equiv.congrProd ac.toEquiv bd.toEquiv) ?_ with
      resp_rel := ?_
  }
  · intro (a, b)
    simp
    rw [←rank_congr (InitialSegment.ofRelIso ac) a, ←rank_congr (InitialSegment.ofRelIso bd) b]
    rfl
  · simp
    intro ⟨⟨a, b⟩, h₀⟩ ⟨⟨c, d⟩, h₁⟩
    apply ac.resp_rel

def min_le_left' (a b: Ordinal) : min a b ≤ a := by
  cases a with | _ _ a =>
  cases b with | _ _ b =>
  exact ⟨rel_min_hom_left _ _⟩
def min_le_right' (a b: Ordinal) : min a b ≤ b := by
  cases a with | _ _ a =>
  cases b with | _ _ b =>
  exact ⟨rel_min_hom_right _ _⟩

instance : Min Ordinal where
  min := min

instance : IsLawfulMin Ordinal where
  min_le_left := min_le_left'
  min_le_right := min_le_right'

instance : IsSemiLatticeMin Ordinal where
  le_min := by
    intro a b k ka kb
    cases a with | _ A rela =>
    cases b with | _ B relb =>
    cases k with | _ K relk =>
    obtain ⟨ka⟩ := ka
    obtain ⟨kb⟩ := kb
    refine ⟨?_⟩
    simp; simp at ka kb
    exact {
      toFun k := {
        val := (ka k, kb k)
        property := by
          simp;
          rw [rank_congr, rank_congr]
      }
      inj' k₀ k₁ hk := by
        simp at hk
        have := Prod.mk.inj (Subtype.mk.inj hk)
        rw [ka.inj.eq_iff, kb.inj.eq_iff] at this
        exact this.left
      resp_rel := ka.resp_rel
      isInitial := by
        intro k ⟨⟨a, b⟩, h⟩
        simp at h
        show rela a (ka k) -> _
        intro r
        obtain ⟨k₀, rfl⟩ := ka.isInitial _ _ r
        simp
        suffices b = kb k₀ by
          cases this
          exists k₀
        simp at h
        simp at r
        replace r := ka.resp_rel.mpr r
        rw [rank_congr ka, ←rank_congr kb] at h
        symm; exact rank_inj h
    }

end Min

section Max

private def sumToRank : α ⊕ β -> Ordinal
| .inl x => rank relα x
| .inr x => rank relβ x

@[simp] def apply_sumToRank_inl : sumToRank r s (.inl x) = rank r x := rfl
@[simp] def apply_sumToRank_inr : sumToRank r s (.inr x) = rank s x := rfl

def eqv_max : Relation (α ⊕ β) :=
  fun x y => sumToRank relα relβ x = sumToRank relα relβ y

def setoid_max : Setoid (α ⊕ β) :=
  Setoid.eqSetoid.comap (sumToRank relα relβ)

def max_ty := Quotient (setoid_max relα relβ)

def max_ty.toRank : max_ty r s ↪ Ordinal where
  toFun := by
    refine Quotient.lift (sumToRank r s) ?_
    intro a b
    exact id
  inj' := by
    intro x y h
    cases x using Quotient.ind with | _ x =>
    cases y using Quotient.ind with | _ y =>
    apply Quotient.sound
    assumption

def rel_max : Relation (max_ty relα relβ) :=
  fun a b => a.toRank < b.toRank

def rel_max_emb : rel_max r s ↪r (· < ·: Relation Ordinal) where
  toEmbedding := max_ty.toRank
  resp_rel := Iff.rfl

def rel_max_hom (h: r ≃r t) (g: s ≃r u) : rel_max r s →r rel_max t u where
  toFun := by
    refine Quotient.lift (Quotient.mk _ ∘ ?_) ?_
    · intro x
      apply Equiv.congrSum _ _ x
      exact h.toEquiv
      exact g.toEquiv
    · intro a b eqv
      apply Quotient.sound
      simp
      cases a <;> cases b
      all_goals
        show rank _ (RelIso.toInitial _ _) = rank _ (RelIso.toInitial _ _)
        rwa [rank_congr, rank_congr]
  resp_rel := by
    intro a b rel
    induction a using Quotient.ind with | _ a =>
    induction b using Quotient.ind with | _ b =>
    show sumToRank _ _ _ < sumToRank _ _ _
    cases a <;> cases b
    all_goals
      show rank _ (RelIso.toInitial _ _) < rank _ (RelIso.toInitial _ _)
      rwa [rank_congr, rank_congr]

instance : Relation.IsWellOrder (rel_max r s) := rel_max_emb.lift_wo

def max : Ordinal -> Ordinal -> Ordinal := by
  refine lift₂ ?_ ?_
  · intro α β relα relβ _ _
    exact type (rel_max relα relβ)
  · intro A B C D rela relb relc reld _ _ _ _ ac bd
    apply sound
    exact {
      toFun := rel_max_hom ac bd
      invFun := rel_max_hom ac.symm bd.symm
      leftInv := by
        intro x
        cases x using Quotient.ind with | _ x =>
        cases x
        all_goals
          apply Quotient.sound
          simp
          rfl
      rightInv := by
        intro x
        cases x using Quotient.ind with | _ x =>
        cases x
        all_goals
          apply Quotient.sound
          simp
          rfl
      resp_rel := by
        intro x y
        apply Iff.intro
        apply (rel_max_hom _ _).resp_rel
        intro h
        let f := (rel_max_hom ac bd).comp (rel_max_hom ac.symm bd.symm)
        replace h : rel_max rela relb (f x) (f y) := (rel_max_hom ac.symm bd.symm).resp_rel h
        simp at h
        have : ∀x, f x = x := ?_
        simpa [this] using h
        clear x y h
        intro x
        cases x using Quotient.ind with | _ x =>
        cases x
        all_goals
          apply Quotient.sound
          simp [f]
          rfl
    }

instance : Max Ordinal := ⟨max⟩

protected def le_max_left (a b : Ordinal) : a ≤ a ⊔ b := by
  cases a with | _ α relα =>
  cases b with | _ β relβ =>
  refine ⟨?_⟩
  simp
  exact {
    toFun x := Quotient.mk _ (.inl x)
    inj' := by
      intro x y h
      simp at h
      replace h : _ = _ := Quotient.exact h
      simp at h
      exact rank_inj h
    resp_rel := by
      intro x y
      show relα x y ↔ rank _ _ < rank _ _
      rw [rank_lt_rank_iff]
    isInitial := by
      intro a b h
      simp
      simp at h
      cases b using Quotient.ind with | _ b =>
      replace h : _ < rank _ _ := h
      have ⟨b', h⟩ := rank_surj relα _ (lt_trans h (rank_lt_type _))
      exists b'
      apply Quotient.sound
      assumption
  }

protected def le_max_right (a b : Ordinal) : b ≤ a ⊔ b := by
  cases a with | _ α relα =>
  cases b with | _ β relβ =>
  refine ⟨?_⟩
  simp
  exact {
    toFun x := Quotient.mk _ (.inr x)
    inj' := by
      intro x y h
      simp at h
      replace h : _ = _ := Quotient.exact h
      simp at h
      exact rank_inj h
    resp_rel := by
      intro x y
      show relβ x y ↔ rank _ _ < rank _ _
      rw [rank_lt_rank_iff]
    isInitial := by
      intro a b h
      simp
      simp at h
      cases b using Quotient.ind with | _ b =>
      replace h : _ < rank _ _ := h
      have ⟨b', h⟩ := rank_surj relβ _ (lt_trans h (rank_lt_type _))
      exists b'
      apply Quotient.sound
      assumption
  }

instance : IsSemiLatticeMax Ordinal where
  le_max_left := Ordinal.le_max_left
  le_max_right := Ordinal.le_max_right
  max_le := by
    intro a b k ak bk
    cases a with | _ A rela =>
    cases b with | _ B relb =>
    cases k with | _ K relk =>
    obtain ⟨ak⟩ := ak
    obtain ⟨bk⟩ := bk
    simp at ak bk
    refine ⟨?_⟩
    simp
    exact {
      toFun := by
        refine Quotient.lift ?_ ?_
        intro x
        exact x.casesOn ak bk
        intro a b h
        cases a <;> cases b <;> simp
        all_goals
          replace h : rank _ _ = rank _ _ := h
          apply rank_inj_initial
          symm; rwa [rank_congr]
      inj' := by
        intro x y h
        cases x using Quotient.ind with | _ x =>
        cases y using Quotient.ind with | _ y =>
        cases x <;> cases y
        all_goals
          apply Quotient.sound
          show _ = _
          simp
        · replace h : ak _ = ak _ := h
          congr
          rwa [ak.inj.eq_iff] at h
        · replace h : ak _ = bk _ := h
          rw [←rank_congr ak, ←rank_congr bk, h]
        · replace h : bk _ = ak _ := h
          rw [←rank_congr ak, ←rank_congr bk, h]
        · replace h : bk _ = bk _ := h
          congr
          rwa [bk.inj.eq_iff] at h
      resp_rel := by
        intro x y
        cases x using Quotient.ind with | _ x =>
        cases y using Quotient.ind with | _ y =>
        show sumToRank _ _ _ < sumToRank _ _ _ ↔ relk (x.casesOn ak bk) (y.casesOn ak bk)
        cases x <;> cases y <;> simp
        all_goals rw [←rank_lt_rank_iff (r := relk), rank_congr, rank_congr]
      isInitial := by
        intro x k h
        cases x using Quotient.ind with | _ x =>
        replace h : relk k (x.casesOn ak bk) := h
        cases x
        replace h : k ∈ Set.range ak := ak.isInitial _ _ h
        obtain ⟨k', rfl⟩ := h
        exists Quotient.mk _ (Sum.inl k')
        replace h : k ∈ Set.range bk := bk.isInitial _ _ h
        obtain ⟨k', rfl⟩ := h
        exists Quotient.mk _ (Sum.inr k')
    }

end Max

instance : IsLinearLattice Ordinal where

end Lattice

section Nat

def ofNat (n: ℕ) : Ordinal := type (· < (·: Fin n))
def omega : Ordinal := type (· < (·: Nat))
abbrev omega' : Ordinal := omega.ulift

notation "ω" => omega'

instance : NatCast Ordinal := ⟨fun n => (ofNat n).ulift⟩
instance : OfNat Ordinal n := ⟨n⟩

def natCast_lt_omega (n: ℕ) : n < ω := by
  refine ⟨?_⟩
  simp
  apply PrincipalSegment.congr
  symm; apply rel_ulift_eqv
  symm; apply rel_ulift_eqv
  refine {
    Fin.embedNat with
    resp_rel := Iff.rfl
    exists_top := by
      exists n
      intro x
      simp
      apply Iff.intro
      intro h
      exists ⟨_, h⟩
      rintro ⟨⟨x, hx⟩, rfl⟩
      assumption
  }

inductive rel_succ : Relation (Option α) where
| some : rel a b -> rel_succ (.some a) (.some b)
| none : rel_succ (.some x) .none

@[simp]
def rel_succ_some_iff : rel_succ r (some a) (some b) ↔ r a b := by
  apply Iff.intro
  intro h; cases h
  assumption
  apply rel_succ.some

@[simp]
def rel_succ_some_none : rel_succ r (some a) .none := by
  apply rel_succ.none


@[simp]
def rel_succ_none_some : ¬rel_succ r .none (some a) := by
  nofun

def rel_succ_eqv : rel_succ rel ≃r Sum.Lex rel (Relation.empty (α := Unit)) where
  toEquiv := (Equiv.option_equiv_unit_sum _).trans (Equiv.commSum _ _)
  resp_rel := by
    intro a b
    simp
    cases a <;> cases b
    apply Iff.intro nofun nofun
    apply Iff.intro nofun nofun
    apply Iff.intro
    intro; apply Sum.Lex.sep
    intro; apply rel_succ.none
    apply Iff.intro
    intro h; cases h
    apply Sum.Lex.inl
    assumption
    intro h; cases h
    apply rel_succ.some
    assumption

def rel_succ_congr (h: r ≃r s)   : rel_succ r ≃r rel_succ s := by
  apply (rel_succ_eqv _).trans
  apply RelIso.trans _ (rel_succ_eqv _).symm
  apply RelIso.congrSumLex
  assumption
  rfl

instance : Relation.IsWellOrder (rel_succ rel) :=
  (rel_succ_eqv rel).toRelEmbedding.lift_wo

def succ : Ordinal -> Ordinal := by
  refine lift (fun _ rel _ => type (rel_succ rel)) ?_
  intro a b rela relb _ _ h
  simp; apply sound
  apply rel_succ_congr
  assumption

def natCast_add (n m: ℕ) : (n + m: Ordinal) = (n + m: ℕ) := by
  apply sound
  simp
  apply flip RelIso.trans
  symm; apply rel_ulift_eqv
  apply RelIso.trans
  apply RelIso.congrSumLex
  apply rel_ulift_eqv
  apply rel_ulift_eqv
  refine { Equiv.finSum with resp_rel := ?_ }
  intro a b
  simp
  apply Iff.intro
  · intro h
    cases h
    · assumption
    · simp;
      apply Nat.add_lt_add_left
      assumption
    · simp
      rename_i a b
      show a.val  < n + b.val
      omega
  · intro h
    cases a <;> cases b <;> simp at *
    assumption
    rename_i a b
    have : n + a.val < b.val := h
    omega
    apply Nat.add_lt_add_iff_left.mp
    assumption

def natCast_mul (n m: ℕ) : (n * m: Ordinal) = (n * m: ℕ) := by
  apply sound
  simp
  apply flip RelIso.trans
  symm; apply rel_ulift_eqv
  apply RelIso.trans
  apply RelIso.congrProdLex
  apply rel_ulift_eqv
  apply rel_ulift_eqv
  refine { Equiv.finProd with resp_rel := ?_ }
  intro a b
  simp
  apply Iff.intro
  · intro h
    cases h
    · simp [Equiv.finProd, Fin.pair]
      apply Nat.lt_of_lt_of_le
      apply Nat.add_lt_add_left
      apply Fin.isLt
      apply flip Nat.le_trans
      apply Nat.le_add_right
      rw [←Nat.succ_mul]
      simp
      apply Nat.mul_le_mul
      omega
      rfl
    · simpa [Equiv.finProd, Fin.pair]
  · obtain ⟨a₀, a₁⟩ := a
    obtain ⟨b₀, b₁⟩ := b
    intro h
    simp [Equiv.finProd, Fin.pair] at h
    rcases lt_trichotomy a₀.val b₀.val with g | g | g
    apply Prod.Lex.left
    assumption
    rw [Fin.val_inj] at g; cases g
    apply Prod.Lex.right
    omega
    rw [←Nat.succ_le] at g
    have : (b₀.val + 1) * m + a₁.val < b₀.val * m + b₁.val := Nat.lt_of_le_of_lt (by
      apply Nat.add_le_add_right
      apply Nat.mul_le_mul_right
      assumption) h
    have : b₀.val * m + b₁.val < (b₀.val + 1) * m := by
      rw [Nat.succ_mul]
      omega
    omega

@[simp]
def succ_eq_add_one (o: Ordinal): o.succ = o + 1 := by
  cases o with | _ α rel =>
  apply sound
  simp
  apply flip RelIso.trans
  apply RelIso.congrSumLex
  rfl; symm; apply rel_ulift_eqv
  apply (rel_succ_eqv _).trans
  apply RelIso.congrSumLex
  rfl
  exact {
    Equiv.unique _ _ with
    resp_rel := by
      intro x y
      simp
  }

@[simp]
def natCast_succ (n: ℕ) : (n: Ordinal) + 1 = (n + 1: ℕ) := by
  rw [←natCast_add]
  congr

def zero_le (o: Ordinal) : 0 ≤ o := by
  cases o with | _ A rel =>
  refine ⟨?_⟩
  simp
  apply InitialSegment.congr
  symm; apply rel_ulift_eqv
  rfl
  refine {
    Embedding.empty with
    resp_rel := by intro x; exact x.elim0
    isInitial := by intro x; exact x.elim0
  }

def natCast_eq_ulift_natCast (n: ℕ) : n = ulift.{u, 0} n := by
  apply sound
  simp
  apply RelIso.trans
  apply rel_ulift_eqv
  apply flip RelIso.trans
  symm; apply rel_ulift_eqv
  apply flip RelIso.trans
  symm; apply rel_ulift_eqv
  rfl

def natCast_inj : Function.Injective fun n: ℕ => (n: Ordinal) := by
  intro x y h
  simp at h
  have ⟨h⟩ := exact h
  simp at h
  replace h := Equiv.trans (Equiv.trans (Equiv.ulift _).symm (h.toEquiv)) (Equiv.ulift _)
  exact Fin.eq_of_equiv h

def natCast_le_natCast_iff (n m: ℕ) : (n: Ordinal) ≤ m ↔ n ≤ m := by
  apply Iff.intro
  intro ⟨h⟩
  simp at h
  have h := Equiv.congrEmbed (Equiv.ulift _) (Equiv.ulift _) h.toEmbedding
  exact Fin.le_of_emebd h
  intro h
  refine ⟨?_⟩
  simp; apply InitialSegment.congr (rel_ulift_eqv _).symm (rel_ulift_eqv _).symm
  refine {
    toFun x := x.castLE h
    inj' := by
      intro x y h
      rw [←Fin.val_inj] at *
      simp at h; assumption
    resp_rel := Iff.rfl
    isInitial := by
      intro a b
      simp
      intro g
      replace g : b.val < a.val := g
      exists ⟨b.val, ?_⟩
      omega
      rfl
  }
def natCast_lt_natCast_iff (n m: ℕ) : (n: Ordinal) < m ↔ n < m := by
  apply lt_iff_of_le_iff
  apply natCast_le_natCast_iff

def lt_natCast (n: ℕ) (o: Ordinal) : o < n ↔ ∃i < n, o = i := by
  apply flip Iff.intro
  rintro ⟨i, hi, rfl⟩
  rwa [natCast_lt_natCast_iff]
  cases o with | _ A rel =>
  intro ⟨h⟩
  simp at h
  replace h := h.congr .refl (rel_ulift_eqv _)
  have ⟨⟨top, topLt⟩, htop⟩ := h.exists_top
  exists top
  apply And.intro
  exact topLt
  have hx_lt_top (x: A) : (h x).val < top := (htop (h x)).mpr Set.mem_range'
  have hx (x: Fin top) : ⟨x.val, (by omega)⟩ ∈ Set.range h  := (htop ⟨x.val, by omega⟩).mp x.isLt
  replace hx := Classical.axiomOfChoice hx
  obtain ⟨f, hf⟩ := hx
  apply sound
  apply RelIso.trans _ (rel_ulift_eqv _).symm
  simp
  exact {
    toFun x := ⟨h x, hx_lt_top x⟩
    invFun := f
    leftInv := by
      intro a
      simp; apply h.inj
      rw [←hf]
    rightInv := by
      intro x; simp
      congr 1
      rw [←hf]
    resp_rel := h.resp_rel
  }

def of_lt_omega (o: Ordinal) : o < ω -> ∃n: ℕ, o = n := by
  cases o with | _ A rel =>
  intro ⟨h⟩
  simp at h
  replace h := h.congr .refl (rel_ulift_eqv _)
  obtain ⟨n, nspec⟩ := h.exists_top
  have (i: Fin n) := (nspec i.val).mp i.isLt
  replace := Classical.axiomOfChoice this
  obtain ⟨f, hf⟩ := this
  exists n
  apply sound
  simp
  apply flip RelIso.trans
  symm; apply rel_ulift_eqv
  simp at hf
  refine {
    toFun a := {
      val := h a
      isLt := by
        apply (nspec _).mpr
        apply Set.mem_range'
    }
    invFun := f
    leftInv x := by
      simp
      apply h.inj
      symm; apply hf ⟨_, _⟩
    rightInv x := by simp; congr; rw [hf]
    resp_rel := by
      intro a b
      apply h.resp_rel
  }

def lt_omega {o: Ordinal} : o < ω ↔ ∃n: ℕ, o = n := by
  apply Iff.intro
  apply of_lt_omega
  rintro ⟨n, rfl⟩
  apply natCast_lt_omega

def lt_succ_self (o: Ordinal) : o < o + 1 := by
  rw [←succ_eq_add_one]
  cases o with | _ A rel =>
  refine ⟨?_⟩
  simp; exact {
    Embedding.optionSome with
    resp_rel := by
      intro x y
      simp
    exists_top := by
      exists .none
      intro a
      apply Iff.intro
      intro h ; cases h
      apply Set.mem_range'
      rintro ⟨x, rfl⟩
      apply rel_succ.none
  }

@[simp]
def ulift_succ (o: Ordinal.{u}) : (ulift.{v} o).succ = ulift.{v} o.succ := by
  cases o with | _ _ r =>
  apply sound
  simp
  apply RelIso.trans _ (rel_ulift_eqv _).symm
  apply RelIso.trans
  apply rel_succ_congr
  apply rel_ulift_eqv
  rfl

@[simp]
def ulift_add (a b: Ordinal.{u}) : (ulift.{v} a) + ulift.{v} b = ulift.{v} (a + b) := by
  cases a with | _ _ rela =>
  cases b with | _ _ relb =>
  apply sound
  simp
  apply RelIso.trans _ (rel_ulift_eqv _).symm
  apply RelIso.trans
  apply RelIso.congrSumLex
  apply rel_ulift_eqv
  apply rel_ulift_eqv
  rfl

def ulift_natCast (n: ℕ) : ulift.{v, u} n = n := by
  apply sound
  simp
  apply RelIso.trans
  apply rel_ulift_eqv
  apply RelIso.trans
  apply rel_ulift_eqv
  apply flip RelIso.trans
  symm; apply rel_ulift_eqv
  rfl

def ofNat_eq_natCast (n: ℕ) : OfNat.ofNat n = (n: Ordinal) := rfl
def natCast_eq_ulift_ofNat (n: ℕ) : (n: Ordinal) = ulift (ofNat n) := rfl

def ofNat_eq_rankNat (n: ℕ) : ofNat n = rank (· < ·) n := by
  apply sound
  exact {
    Equiv.fin_equiv_nat_subtype (n := n) with
    resp_rel := Iff.rfl
  }
def natCast_eq_rankNat (n: ℕ) : n = ulift (rank (· < ·) n) := by rw [←ofNat_eq_rankNat]; rfl

def le_of_lt_succ {a b: Ordinal} : a < b + 1 -> a ≤ b := by
  cases a with | _ A rela =>
  cases b with | _ B relb =>
  rw [←succ_eq_add_one]
  intro ⟨ab⟩; simp at ab
  have ⟨top, htop⟩ := ab.exists_top
  have ne_none (a: A) : (ab a).isSome := by
    apply Option.isSome_iff_ne_none.mpr
    intro g
    have := (htop (ab a)).mpr Set.mem_range'
    rw [g] at this
    nomatch this

  refine ⟨?_⟩; simp
  refine {
    toFun a := (ab a).get (ne_none a)
    inj' a b h := ab.inj (Option.get_inj.mp h)
    resp_rel := by
      intro a b
      simp
      rw [←rel_succ_some_iff (r := relb)]
      simp
      apply ab.resp_rel
    isInitial := by
      intro a b h
      simp at h
      rw [←rel_succ_some_iff (r := relb)] at h
      simp at h
      have ⟨a', heq⟩ := ab.init _ _ h
      exists a'
      simp
      apply Option.some.inj
      simp [heq]
  }

def lt_succ_of_le {a b: Ordinal} : a ≤ b -> a < b + 1 := by
  if ha:b ≤ a then
    intro h
    cases le_antisymm h ha
    apply lt_succ_self
  else
    rw [not_le] at ha
    intro ha; clear ha
    apply lt_trans ha
    apply lt_succ_self

def lt_succ {a b: Ordinal} : a < b + 1 ↔ a ≤ b := by
  apply Iff.intro
  apply le_of_lt_succ
  apply lt_succ_of_le

def succ_le_of_lt {a b: Ordinal} (h: a < b) : a + 1 ≤ b := by
  rw [←succ_eq_add_one]
  cases a with | _ A rela =>
  cases b with | _ B relb =>
  obtain ⟨h⟩ := h; simp at h
  have ⟨top, htop⟩ := h.exists_top
  refine ⟨?_⟩; simp
  exact {
    toFun
    | .some x => h x
    | .none => top
    inj' := by
      intro x y g
      cases x <;> cases y <;> simp at g
      rfl
      rename_i x
      have := (htop (h x)).mpr Set.mem_range'
      rw [←g] at this
      have := Relation.irrefl this
      contradiction
      rename_i x
      have := (htop (h x)).mpr Set.mem_range'
      rw [←g] at this
      have := Relation.irrefl this
      contradiction
      rw [h.inj g]
    resp_rel := by
      intro x y
      cases x <;> cases y <;> simp
      apply Iff.intro
      exact nofun
      intro g; have := Relation.irrefl g; contradiction
      intro g; rename_i x
      have := (htop (h x)).mpr Set.mem_range'
      have := Relation.asymm this
      contradiction
      apply (htop _).mpr Set.mem_range'
      apply h.resp_rel
    isInitial := by
      intro a b
      cases a <;> simp
      intro hx
      have ⟨a, ha⟩ := (htop b).mp hx
      exists a
      intro hx
      have ⟨a, ha⟩ := h.init _ _ hx
      exists .some a
  }

def succ_lt_succ {a b : Ordinal} (h: a < b) : a + 1 < b + 1 := by
  apply lt_succ_of_le
  apply succ_le_of_lt
  assumption

def succ_inj : Function.Injective succ := by
  intro x y h
  simp at h
  rcases lt_trichotomy x y with g | g | g
  · have := succ_lt_succ g
    rw [h] at this
    have := lt_irrefl this
    contradiction
  · assumption
  · have := succ_lt_succ g
    rw [h] at this
    have := lt_irrefl this
    contradiction

def add_left_strict_mono (k: Ordinal) : StrictMonotone (k + ·) := by
  intro a b
  cases a with | _ α relα =>
  cases b with | _ β relβ =>
  cases k with | _ κ relκ =>
  intro ⟨f⟩
  simp at f
  refine ⟨?_⟩
  simp
  exact {
    toFun
    | .inl x => .inl x
    | .inr x => .inr (f x)
    inj' := by
      intro x y h
      cases x <;> cases y <;> simp at h
      congr
      rw [f.inj.eq_iff] at h
      congr
    resp_rel := by
      intro x y
      cases x <;> cases y <;> simp
      apply f.resp_rel
    exists_top := by
      have ⟨b, btop⟩ := f.exists_top
      exists .inr b
      intro x
      cases x
      simp
      rename_i k
      exists .inl k
      simp
      rw [btop]
      apply Iff.intro
      rintro ⟨a, rfl⟩
      exists .inr a
      intro ⟨a, ha⟩
      cases a <;> simp at ha
      subst ha
      apply Set.mem_range'
  }

def add_left_mono (k: Ordinal) : Monotone (k + ·) := by
  intro x y
  apply (add_left_strict_mono _).le_iff_le.mpr

def add_right_mono (k: Ordinal) : Monotone (· + k) := by
  intro a b
  cases a with | _ α relα =>
  cases b with | _ β relβ =>
  cases k with | _ κ relκ =>
  intro ⟨f⟩
  simp at f
  apply InitialSegment.collapse
  refine ⟨?_⟩
  simp
  exact {
    toFun
    | .inl x => .inl (f x)
    | .inr x => .inr x
    inj' := by
      intro x y h
      cases x <;> cases y <;> simp at h
      congr
      rwa [f.inj.eq_iff] at h
      congr
    resp_rel := by
      intro x y
      cases x <;> cases y <;> simp
      apply f.resp_rel
  }

def mul_right_mono (k: Ordinal) : Monotone (· * k) := by
  intro a b
  cases a with | _ α relα =>
  cases b with | _ β relβ =>
  cases k with | _ κ relκ =>
  intro ⟨f⟩
  simp at f
  apply InitialSegment.collapse
  refine ⟨?_⟩
  simp
  exact {
    toFun x := (f x.1, x.2)
    inj' := by
      intro x y h
      simp at h
      rw [f.inj.eq_iff] at h
      ext; exact h.left; exact h.right
    resp_rel := by
      intro x y
      simp
      apply Iff.intro
      · intro h
        cases h
        apply Prod.Lex.left
        apply f.resp_rel.mp
        assumption
        apply Prod.Lex.right
        assumption
      · generalize hx₀:f x.fst = x₀
        generalize hy₀:f y.fst = y₀
        intro h
        cases h
        apply Prod.Lex.left
        subst x₀ y₀
        apply f.resp_rel.mpr
        assumption
        subst x₀
        obtain ⟨x₀, x₁⟩ := x
        obtain ⟨y₀, y₁⟩ := y
        simp at *
        rw [f.inj.eq_iff] at hy₀
        cases hy₀
        apply Prod.Lex.right
        assumption
  }

def mul_left_mono (k: Ordinal) : Monotone (k * ·) := by
  intro a b
  cases a with | _ α relα =>
  cases b with | _ β relβ =>
  cases k with | _ κ relκ =>
  intro ⟨f⟩
  simp at f
  apply InitialSegment.collapse
  refine ⟨?_⟩
  simp
  exact {
    toFun x := (x.1, f x.2)
    inj' := by
      intro x y h
      simp at h
      rw [f.inj.eq_iff] at h
      ext; exact h.left; exact h.right
    resp_rel := by
      intro x y
      simp
      apply Iff.intro
      · intro h
        cases h
        apply Prod.Lex.left
        assumption
        apply Prod.Lex.right
        apply f.resp_rel.mp
        assumption
      · obtain ⟨x₀, x₁⟩ := x
        obtain ⟨y₀, y₁⟩ := y
        intro h
        cases h
        apply Prod.Lex.left
        assumption
        apply Prod.Lex.right
        apply f.resp_rel.mpr
        assumption
  }

def le_iff_add_left {k a b: Ordinal} : a ≤ b ↔ k + a ≤ k + b := by
  apply (add_left_strict_mono k).le_iff_le.symm

def lt_iff_add_left {k a b: Ordinal} : a < b ↔ k + a < k + b := by
  apply (add_left_strict_mono k).lt_iff_lt.symm

def addLeft (a: Ordinal) : Ordinal ↪o Ordinal where
  toFun x := a + x
  inj' := (add_left_strict_mono a).Injective
  map_le _ _ := le_iff_add_left

def ofPre_eq_zero_iff (p: Pre) : IsEmpty p.ty ↔ ofPre p = 0 := by
  apply Iff.intro
  intro h
  apply sound
  exact {
    Equiv.empty with
    resp_rel {x} := elim_empty x
  }
  intro h
  have ⟨h⟩  := exact h
  simp at h
  exact { elim x := elim_empty (h x) }

def type_eq_zero_iff : IsEmpty α ↔ type rel = 0 := ofPre_eq_zero_iff {
  ty := α
  rel := rel
}

@[simp] def zero_add (a: Ordinal) : 0 + a = a := by
  cases a with | _ a rela =>
  apply sound
  simp
  apply RelIso.trans
  apply RelIso.congrSumLex
  apply rel_ulift_eqv
  rfl
  symm
  exact {
    toFun := .inr
    invFun
    | .inl x => nomatch x
    | .inr x => x
    leftInv _ := rfl
    rightInv
    | .inl x => nomatch x
    | .inr x => rfl
    resp_rel := by simp [resp_rel]
  }
@[simp] def add_zero (a: Ordinal) : a + 0 = a := by
  cases a
  apply sound
  simp
  apply RelIso.trans
  apply RelIso.congrSumLex
  rfl
  apply rel_ulift_eqv
  symm
  exact {
    toFun := .inl
    invFun
    | .inr x => nomatch x
    | .inl x => x
    leftInv _ := rfl
    rightInv
    | .inr x => nomatch x
    | .inl x => rfl
    resp_rel := by simp [resp_rel]
  }

end Nat

section BasicArith

def add_max (a b k: Ordinal) : k + (a ⊔ b) = (k + a) ⊔ (k + b) := by
  open scoped Classical in
  rw [max_def, max_def]
  split; rename_i h
  rw [if_pos]
  apply add_left_mono
  assumption
  rename_i h
  split
  apply le_antisymm
  assumption
  apply add_left_mono
  apply le_of_not_le
  assumption
  rfl

def mul_max (a b k: Ordinal) : k * (a ⊔ b) = (k * a) ⊔ (k * b) := by
  open scoped Classical in
  rw [max_def, max_def]
  split; rename_i h
  rw [if_pos]
  apply mul_left_mono
  assumption
  rename_i h
  split
  apply le_antisymm
  assumption
  apply mul_left_mono
  apply le_of_not_le
  assumption
  rfl

def max_add (a b k: Ordinal) : (a ⊔ b) + k = (a + k) ⊔ (b + k) := by
  open scoped Classical in
  rw [max_def, max_def]
  split; rename_i h
  rw [if_pos]
  apply add_right_mono
  assumption
  rename_i h
  split
  apply le_antisymm
  assumption
  apply add_right_mono
  apply le_of_not_le
  assumption
  rfl

def max_mul (a b k: Ordinal) : (a ⊔ b) * k = (a * k) ⊔ (b * k) := by
  open scoped Classical in
  rw [max_def, max_def]
  split; rename_i h
  rw [if_pos]
  apply mul_right_mono
  assumption
  rename_i h
  split
  apply le_antisymm
  assumption
  apply mul_right_mono
  apply le_of_not_le
  assumption
  rfl

def add_min (a b k: Ordinal) : k + (a ⊓ b) = (k + a) ⊓ (k + b) := by
  open scoped Classical in
  rw [min_def, min_def]
  split; rename_i h
  rw [if_pos]
  apply add_left_mono
  assumption
  rename_i h
  split
  apply le_antisymm
  apply add_left_mono
  apply le_of_not_le
  assumption
  assumption
  rfl

def mul_min (a b k: Ordinal) : k * (a ⊓ b) = (k * a) ⊓ (k * b) := by
  open scoped Classical in
  rw [min_def, min_def]
  split; rename_i h
  rw [if_pos]
  apply mul_left_mono
  assumption
  rename_i h
  split
  apply le_antisymm
  apply mul_left_mono
  apply le_of_not_le
  assumption
  assumption
  rfl

def min_add (a b k: Ordinal) : (a ⊓ b) + k = (a + k) ⊓ (b + k) := by
  open scoped Classical in
  rw [min_def, min_def]
  split; rename_i h
  rw [if_pos]
  apply add_right_mono
  assumption
  rename_i h
  split
  apply le_antisymm
  apply add_right_mono
  apply le_of_not_le
  assumption
  assumption
  rfl

def min_mul (a b k: Ordinal) : (a ⊓ b) * k = (a * k) ⊓ (b * k) := by
  open scoped Classical in
  rw [min_def, min_def]
  split; rename_i h
  rw [if_pos]
  apply mul_right_mono
  assumption
  rename_i h
  split
  apply le_antisymm
  apply mul_right_mono
  apply le_of_not_le
  assumption
  assumption
  rfl

def add_mul (a b k: Ordinal) : (a + b) * k = a * k + b * k := by
  cases a with | _ α rela =>
  cases b with | _ β relb =>
  cases k with | _ κ relk =>
  apply sound
  simp
  refine {
    Equiv.sum_prod _ _ _ with
    resp_rel := ?_
  }
  intro (x, k₀) (y, k₁)
  cases x <;> cases y <;> (simp; rename_i x y)
  · apply Iff.intro
    · intro h
      cases h <;> rename_i h
      cases h
      apply Prod.Lex.left
      assumption
      apply Prod.Lex.right
      assumption
    · intro h
      cases h <;> rename_i h
      apply Prod.Lex.left
      simpa
      apply Prod.Lex.right
      assumption
  · apply Prod.Lex.left
    apply Sum.Lex.sep
  · nofun
  · apply Iff.intro
    · intro h
      cases h <;> rename_i h
      cases h
      apply Prod.Lex.left
      assumption
      apply Prod.Lex.right
      assumption
    · intro h
      cases h <;> rename_i h
      apply Prod.Lex.left
      simpa
      apply Prod.Lex.right
      assumption

def add_assoc (a b c: Ordinal) : a + b + c = a + (b + c) := by
  cases a with | _ α rela =>
  cases b with | _ β relb =>
  cases c with | _ γ relc =>
  apply sound
  simp
  refine {
    (Equiv.sum_assoc _ _ _).symm with
    resp_rel := ?_
  }
  intro x y
  rcases x with (x | x) | x <;> rcases y with (y | y) | y
  all_goals simp [Equiv.sum_assoc]

def mul_assoc (a b c: Ordinal) : a * b * c = a * (b * c) := by
  cases a with | _ α rela =>
  cases b with | _ β relb =>
  cases c with | _ γ relc =>
  apply sound
  simp
  refine {
    (Equiv.prod_assoc _ _ _).symm with
    resp_rel := ?_
  }
  intro ((_, _), _) ((_, _), _)
  simp [Equiv.prod_assoc]
  apply Iff.intro
  · intro h
    cases h <;> rename_i h
    cases h
    apply Prod.Lex.left
    assumption
    apply Prod.Lex.right
    apply Prod.Lex.left
    assumption
    apply Prod.Lex.right
    apply Prod.Lex.right
    assumption
  · intro h
    cases h <;> rename_i h
    apply Prod.Lex.left
    apply Prod.Lex.left
    assumption
    cases h
    apply Prod.Lex.left
    apply Prod.Lex.right
    assumption
    apply Prod.Lex.right
    assumption

end BasicArith

section Limit

class IsLimitOrdinal (o: Ordinal) where
  protected ne_succ: ∀x < o, x.succ ≠ o

class IsSuccLimitOrdinal (o: Ordinal) extends IsLimitOrdinal o, NeZero o where

def succ_lt_limit (o: Ordinal) (h: IsLimitOrdinal o := by infer_instance) : ∀x < o, x + 1 < o := by
  intro x hx
  rcases lt_trichotomy (x + 1) o with g | g | g
  assumption
  have := h.ne_succ x hx (by simp [g])
  contradiction
  have := lt_of_lt_of_le hx (le_of_lt_succ g)
  have := lt_irrefl this
  contradiction

def limit_ne_succ (o: Ordinal) [h: IsLimitOrdinal o] : ∀x, x + 1 ≠ o := by
  intro x g
  have := h.ne_succ
  rcases lt_trichotomy x o with h₀ | h₀ | h₀
  have := this x h₀
  simp [g] at this
  subst o
  have := lt_succ_self x
  rw [←h₀] at this
  exact lt_irrefl this
  rw [←g] at h₀
  have := lt_asymm (lt_succ_self x)
  contradiction

def nomax (h: IsLimitOrdinal (type rel)) : ∀x, ∃y, rel x y := by
  intro x
  have := succ_lt_limit (type rel) inferInstance (Ordinal.rank rel x) (rank_lt_type _)
  replace ⟨o, ho⟩ := rank_surj rel (rank rel x + 1) this
  exists o
  apply rank_lt_rank_iff.mp
  rw [←ho]
  apply lt_succ_self

instance : IsLimitOrdinal 0 where
  ne_succ x h g := by
    rw [←not_le] at h
    exact h (zero_le _)

instance : IsSuccLimitOrdinal ω where
  ne_succ x hx  h := by
    rw [lt_omega] at hx
    obtain ⟨n, rfl⟩ := hx
    simp at h
    have := natCast_lt_omega (n + 1)
    rw [h] at this
    exact lt_irrefl this
  out := by
    intro h
    have := natCast_lt_omega 0
    rw [h] at this
    exact lt_irrefl this

noncomputable def rec
  {motive : Ordinal -> Sort*}
  (ind: ∀o, (∀x < o, motive x) -> motive o)
  (o: Ordinal) : motive o := ind o (fun x _hx => rec ind x)
termination_by o

section

variable
  {motive : Ordinal -> Sort*}
  (limit: ∀o, IsLimitOrdinal o -> (∀x < o, motive x) -> motive o)
  (succ: ∀o, motive o -> motive (o + 1))

noncomputable def transfiniteRecursion' (o: Ordinal) : motive o :=
  open scoped Classical in
  if h:∃x, x + 1 = o then
    let x := Classical.choose h
    have hx : x + 1 = o := Classical.choose_spec h
    cast (by rw [hx]) (succ x (transfiniteRecursion' x))
  else
    limit _ { ne_succ x hx g := by exact h ⟨_, succ_eq_add_one _ ▸ g⟩} (fun x hx => transfiniteRecursion' x)
termination_by o
decreasing_by
  · show x < o
    rw [←hx]
    apply lt_succ_self
  · assumption

def transfiniteRecursion'_limit (o: Ordinal) [IsLimitOrdinal o] : transfiniteRecursion' limit succ o = limit o inferInstance (fun x _ => transfiniteRecursion' limit succ x) := by
  rw [transfiniteRecursion']
  simp; rw [dif_neg]
  intro ⟨x, hx⟩
  exact limit_ne_succ o x hx

def transfiniteRecursion'_succ (o: Ordinal) : transfiniteRecursion' limit succ (o + 1) = succ o (transfiniteRecursion' limit succ o) := by
  rw [transfiniteRecursion']
  have : ∃ x, x + 1 = o + 1 := ⟨o, rfl⟩
  rw [dif_pos this]
  simp
  apply cast_eq_of_heq
  congr
  apply succ_inj
  simp;
  rw [Classical.choose_spec this]
  apply succ_inj
  simp;
  rw [Classical.choose_spec this]

end

section

variable
  {motive : Ordinal -> Sort*}
  (zero: motive 0)
  (succ: ∀o, motive o -> motive (o + 1))
  (limit: ∀o, IsSuccLimitOrdinal o -> (∀x < o, motive x) -> motive o)

@[induction_eliminator]
noncomputable def transfiniteRecursion (o: Ordinal) : motive o :=
  transfiniteRecursion' (motive := motive)
    (fun o _ ih =>
      open scoped Classical in
      if h:o = 0 then
        h ▸ zero
      else
        have : NeZero o := ⟨h⟩
        limit _ ⟨⟩ ih)
    succ o

def transfiniteRecursion_zero : transfiniteRecursion zero succ limit 0 = zero := by
  unfold transfiniteRecursion
  rw [transfiniteRecursion'_limit, dif_pos rfl]

def transfiniteRecursion_limit (o: Ordinal) [IsSuccLimitOrdinal o] : transfiniteRecursion zero succ limit o = limit o inferInstance (fun x _ => transfiniteRecursion zero succ limit x) := by
  unfold transfiniteRecursion
  rw [transfiniteRecursion'_limit, dif_neg]
  rename_i h; exact h.out

def transfiniteRecursion_succ (o: Ordinal) : transfiniteRecursion zero succ limit (o + 1) = succ o (transfiniteRecursion zero succ limit o) := by
  rw [transfiniteRecursion, transfiniteRecursion'_succ]
  rfl

end

def exists_limit (o: Ordinal) : ∃x: Ordinal, x ≤ o ∧ x.IsLimitOrdinal ∧ ∀y ≤ o, y.IsLimitOrdinal -> y ≤ x := by
  induction o using transfiniteRecursion' with
  | limit o lim ih =>
    refine ⟨o, ?_, lim, ?_⟩
    rfl
    intro y _ lim
    assumption
  | succ o ih =>
    obtain ⟨x, x_le_o, x_limit, spec⟩ := ih
    exists x
    apply And.intro
    apply le_trans x_le_o
    apply le_of_lt
    apply lt_succ_self
    apply And.intro x_limit
    intro y h ylim
    rcases lt_or_eq_of_le h with h | h
    exact spec _ (le_of_lt_succ h) ylim
    subst y
    have := ylim.ne_succ o (lt_succ_self _) (by simp)
    contradiction

noncomputable
def limit (o: Ordinal) : Ordinal :=
  Classical.choose (exists_limit o)

def limit_le (o: Ordinal) : limit o ≤ o :=
  (Classical.choose_spec (exists_limit o)).left

def limit_is_limit_ord (o: Ordinal) : (limit o).IsLimitOrdinal :=
  (Classical.choose_spec (exists_limit o)).right.left

def limit_is_max_limit_ord (o: Ordinal) : ∀x ≤ o, x.IsLimitOrdinal -> x ≤ limit o :=
  (Classical.choose_spec (exists_limit o)).right.right

def finite_limit (o: Ordinal) : o.IsLimitOrdinal -> o < ω -> o = 0 := by
  intro ho o_lt_omega
  rw [lt_omega] at o_lt_omega
  obtain ⟨n, rfl⟩ := o_lt_omega
  cases n
  rfl
  rename_i n
  have := ho.ne_succ n
  simp [natCast_lt_natCast_iff] at this

end Limit

section ConditionallyCompleteLattice

open scoped Classical

def BoundedBelow (s: Set Ordinal) : s.BoundedBelow := by
  exists 0
  intro x hx
  apply zero_le

instance : Bot Ordinal where
  bot := 0

instance : IsLawfulBot Ordinal where
  bot_le := zero_le

noncomputable instance : InfSet Ordinal where
  sInf S :=
    if hS:S.Nonempty then
      S.min (· < ·) hS
    else
      0

noncomputable instance : SupSet Ordinal where
  sSup S := sInf S.upperBounds

protected def le_csInf (S: Set Ordinal) (x: Ordinal) : S.Nonempty → x ∈ S.lowerBounds → x ≤ ⨅ S := by
  intro hS hx
  apply hx
  simp [sInf]
  rw [dif_pos hS]
  apply Set.min_mem
protected def csInf_le (s: Set Ordinal) (x: Ordinal) : x ∈ s → ⨅ s ≤ x := by
  intro hx
  rw [←not_lt]; intro h
  simp [sInf] at h
  rw [dif_pos ⟨_, hx⟩] at h
  exact Set.not_lt_min _ _ _ hx h

instance : IsConditionallyCompleteLattice Ordinal where
  le_csInf := Ordinal.le_csInf _ _
  csInf_le _ := Ordinal.csInf_le _ _
  le_csSup := by
    intro S a hS ha
    simp [sSup]
    apply Ordinal.le_csInf
    assumption
    intro x hx
    apply hx
    assumption
  csSup_le := by
    intro S a hS ha
    simp [sSup]
    apply Ordinal.csInf_le
    assumption

def omega_eq_sSup_natCast : ω = ⨆n: ℕ, (n: Ordinal) := by
  apply le_antisymm
  · erw [le_csSup_iff]
    · intro x hx
      replace hx : ∀n: ℕ, n ≤ x := by
        intro n
        apply hx
        apply Set.mem_range'
      cases x with | _ A rel =>
      replace hx (n: ℕ) : ∃x, n = rank rel x := by
        apply rank_surj
        apply lt_of_lt_of_le
        apply lt_succ_self
        simp ; apply hx
      replace hx := Classical.axiomOfChoice hx
      obtain ⟨f, hf⟩ := hx
      refine ⟨?_⟩
      simp
      apply InitialSegment.congr
      symm; apply rel_ulift_eqv
      rfl
      exact {
        toFun := f
        inj' := by
          intro x y h
          rw [←(rank_inj (r := rel)).eq_iff, ←hf, ← hf] at h
          apply natCast_inj
          assumption
        resp_rel := by
          intro x y
          simp
          rw [←rank_lt_rank_iff (r := rel), ←hf, ←hf, natCast_lt_natCast_iff]
        isInitial := by
          intro a b h
          simp at h
          rw [←rank_lt_rank_iff (r := rel), ←hf] at h
          rw [lt_natCast] at h
          obtain ⟨i, hi, eq⟩ := h
          exists i
          simp
          apply rank_inj (r := rel)
          rwa [←hf]
      }
    · exists ω
      rintro _ ⟨n, rfl⟩
      apply le_of_lt; apply natCast_lt_omega
    · exists 0
      exists 0
  · apply csSup_le
    exists 0
    exists 0
    rintro _ ⟨i, rfl⟩
    apply le_of_lt; apply natCast_lt_omega

end ConditionallyCompleteLattice

section FundementalSequence

class IsFundementalSequence (f: ℕ -> Ordinal) (o: Ordinal) : Prop where
  lt_ord: ∀n, f n < o
  sup_eq_ord: ⨆i, f i = o
  increasing: StrictMonotone f

structure FundementalSequences where
  toFun: Ordinal -> ℕ -> Ordinal
  spec: ∀o, IsFundementalSequence (toFun o) o

instance : FunLike FundementalSequences Ordinal (ℕ -> Ordinal) where

instance (f: FundementalSequences) (o: Ordinal) : IsFundementalSequence (f o) o := f.spec o

def repeat_fun (f: α -> α) : ℕ -> α -> α
| 0 => id
| n + 1 => f ∘ repeat_fun f n

-- the fast growing heirarchy for a given choice of fundemental sequences
-- https://en.wikipedia.org/wiki/Fast-growing_hierarchy#Definition
noncomputable def fast (f: FundementalSequences) : Ordinal -> ℕ -> ℕ :=
  transfiniteRecursion (motive := fun _ => ℕ -> ℕ)
    Nat.succ
    (fun _ ih => fun n => repeat_fun ih n n)
    (fun o _ ih => fun n => ih (f o n) (IsFundementalSequence.lt_ord _) n)

def fast_zero (f: FundementalSequences) : fast f 0 = Nat.succ := transfiniteRecursion_zero _ _ _
def fast_succ (f: FundementalSequences) (o: Ordinal) : fast f (o + 1) = fun n => repeat_fun (fast f o) n n := transfiniteRecursion_succ _ _ _ _
def fast_limit (f: FundementalSequences) (o: Ordinal) [IsSuccLimitOrdinal o] : fast f o = fun n => (fast f (f o n)) n := transfiniteRecursion_limit _ _ _ _

-- the slow growing heirarchy for a given choice of fundemental sequences
-- https://en.wikipedia.org/wiki/Slow-growing_hierarchy#Definition
noncomputable def slow (f: FundementalSequences) : Ordinal -> ℕ -> ℕ :=
  transfiniteRecursion (motive := fun _ => ℕ -> ℕ)
    (fun _ => 0)
    (fun _ ih => Nat.succ ∘ ih)
    (fun o _ ih => fun n => ih (f o n) (IsFundementalSequence.lt_ord _) n)

def slow_zero (f: FundementalSequences) : slow f 0 = fun _ => 0 := transfiniteRecursion_zero _ _ _
def slow_succ (f: FundementalSequences) (o: Ordinal) : slow f (o + 1) = fun n => slow f o n + 1 := transfiniteRecursion_succ _ _ _ _
def slow_limit (f: FundementalSequences) (o: Ordinal) [IsSuccLimitOrdinal o] : slow f o = fun n => (slow f (f o n)) n := transfiniteRecursion_limit _ _ _ _

def slow_natCast (f: FundementalSequences) (n: ℕ) : slow f n = fun _ => n := by
  ext i
  induction n with
  | zero => erw [slow_zero]
  | succ n ih =>
    rw [←natCast_succ, slow_succ]
    simp
    rw [ih]

end FundementalSequence

section Enum

instance : Relation.IsWellOrder ((· < · : Relation <| Set.Iio (type rel))) :=
  (RelEmbedding.subtype (P := fun o => o < type rel) (· < ·)).lift_wo

-- the ordinals less than `type rel` are isomorphic to `rel`, which provides
noncomputable def enum : (· < · : Relation <| Set.Iio (type rel)) ≃r rel := by
  have (o: Set.Iio (type rel)) := rank_surj rel o.val o.property
  replace := Classical.axiomOfChoice this
  let f := Classical.choose this
  have hf := Classical.choose_spec this
  simp at hf
  exact RelIso.symm {
    toFun x := {
      val := rank rel x
      property := rank_lt_type _
    }
    invFun := f
    leftInv x := by
      simp
      apply rank_inj (r := rel)
      symm; apply hf
      apply rank_lt_type
    rightInv x := by
      simp; symm
      apply Subtype.val_inj
      apply hf
      exact x.property
    resp_rel {a b} := (rank_lt_rank_iff (r := rel)).symm
  }

@[simp]
def symm_apply_enum (a: α) : (enum rel).symm a = ⟨rank rel a, rank_lt_type _⟩ := rfl

@[simp]
def enum_rank : enum rel ⟨rank rel a, rank_lt_type _⟩ = a := by
  apply (enum rel).symm.inj
  simp

def enum_lt_enum : r (enum r a) (enum r b) ↔ a < b := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  obtain ⟨a, rfl⟩ := rank_surj r a ha
  obtain ⟨b, rfl⟩ := rank_surj r b hb
  simp
  show _ ↔ rank r a < rank r b
  rw [rank_lt_rank_iff]

def enum_le_enum : ¬r (enum r a) (enum r b) ↔ b ≤ a := by
  show _ ↔ b.val ≤ a.val
  rw [←not_lt]
  apply Iff.not_iff_not
  show _ ↔ a < b
  rw [←enum_lt_enum]

end Enum

section Ord

-- the ordinal representing the class of all ordinals in universe `u`
-- NOTE: that this lives one universe higher up, since this is a proper class
def ord : Ordinal.{u + 1} := @type Ordinal.{u} (· < ·) _

def lt_ord (o: Ordinal.{u + 1}) : o < ord.{u} ↔ ∃x: Ordinal.{u}, o = ulift.{u+1} x := by
  apply Iff.intro
  · cases o with | _ α rel =>
    intro h
    have ⟨x, hx⟩ := rank_surj _ _ h
    exists x
    rwa [←rank_eq_ulift]
  · rintro ⟨x, rfl⟩
    cases x with | _ α rel =>
    refine ⟨?_⟩
    simp
    apply PrincipalSegment.congr
    symm; apply rel_ulift_eqv
    rfl
    exact {
      toFun := rank rel
      inj' := rank_inj
      resp_rel := rank_lt_rank_iff.symm
      exists_top := by
        exists type rel
        intro x
        simp
        apply Iff.intro
        intro h
        obtain ⟨x, rfl⟩ := rank_surj _ _ h
        apply Set.mem_range'
        rintro ⟨x, rfl⟩
        apply rank_lt_type
    }

def ord_is_minimal (o: Ordinal.{u + 1}) : (∀x: Ordinal.{u}, ulift.{u+1} x ≤ o) -> ord.{u} ≤ o := by
  intro h
  rw [←not_lt, lt_ord]
  rintro ⟨x, rfl⟩
  have := h x.succ
  simp at this
  rw [ulift_le_ulift] at this
  rw [←not_lt] at this
  apply this
  apply lt_succ_self

instance : IsSuccLimitOrdinal ord.{u} where
  ne_succ := by
    intro x h
    rw [lt_ord] at h
    obtain ⟨x, rfl⟩ := h
    rw [ulift_succ]
    intro h
    have : ulift.{u+1} x.succ < ord.{u} := by rw [lt_ord]; exists x.succ
    rw [h] at this
    exact lt_irrefl this
  out := by
    intro h
    have g : ulift.{u + 1, u} 0 = ord.{u} := by rw [ofNat_eq_natCast, ulift_natCast, ←ofNat_eq_natCast, h]
    have : ulift.{u+1, u} 0 < ord.{u} := by rw [lt_ord]; exists 0
    rw [g] at this
    exact lt_irrefl this

def ord_eq_sup_ulift : ord.{u} = ⨆o: Ordinal, ulift.{u+1, u} o := by
  apply flip le_antisymm
  · apply csInf_le
    apply BoundedBelow
    rintro _ ⟨x, rfl⟩
    apply le_of_lt; simp
    apply (lt_ord _).mpr ⟨x, rfl⟩
  · apply ord_is_minimal
    intro x
    apply le_csInf
    exists ord
    rintro _ ⟨x, rfl⟩
    apply le_of_lt; simp
    apply (lt_ord _).mpr ⟨x, rfl⟩
    rintro _ hx
    apply hx
    apply Set.mem_range'

end Ord

section Subtype

@[simp]
def rel_subtype (P: α -> Prop) : Relation (Subtype P) := fun x y => rel x y

instance : Relation.IsWellOrder (rel_subtype rel P) :=
    RelEmbedding.lift_wo (r := rel) {
      Embedding.subtypeVal with
      resp_rel := Iff.rfl
    }

def subtype (P: α -> Prop) : Ordinal := type (rel_subtype rel P)

def subtype_congr (h: r ≃r s) (g: ∀x, P x ↔ Q (h x)) : subtype r P = subtype s Q := by
  apply sound
  refine {
    Equiv.congrSubtype h.toEquiv ?_ with
    resp_rel := h.resp_rel
  }
  assumption

end Subtype

section Sub

def sub : Ordinal -> Ordinal -> Ordinal := by
  let f (α: Type _) (relα: α -> α -> Prop) [Relation.IsWellOrder relα] (b: Ordinal) : Ordinal :=
    subtype relα (fun x => b ≤ rank relα x)
  refine lift f ?_
  intro α β relα relβ _ _ h
  apply funext
  intro o
  apply subtype_congr h
  intro x
  rw [show h x = h.toInitial x from rfl, rank_congr]

instance : Sub Ordinal where
  sub := sub

def sub_of_le (a b: Ordinal) (h: a ≤ b) : a - b = 0 := by
  cases a with | _ α relα =>
  apply (ofPre_eq_zero_iff _).mp
  refine { elim | ⟨x, hx⟩ => ?_ }
  have := le_trans h hx
  rw [←not_lt] at this
  apply this
  apply rank_lt_type

def add_sub_cancel (a b: Ordinal) (h: b ≤ a) : b + (a - b) = a := by
  classical
  cases a with | _ α relα =>
  cases b with | _ β relβ =>
  obtain ⟨f₀⟩ := h
  simp at f₀
  let S := Set.mk fun a => rank relα a < type relβ
  have (a: S) : ∃b: β, a.val = f₀ b := by
    have ⟨b, hb⟩ := rank_surj relβ (rank relα a.val) a.property
    exists b
    apply rank_inj (r := relα)
    rwa [rank_congr]
  replace := Classical.axiomOfChoice this
  obtain ⟨f, hf⟩ := this
  apply sound
  simp
  exact {
    toFun
    | .inl x => f₀ x
    | .inr x => x.val
    invFun x :=
      if hx:rank relα x < type relβ then
        .inl (f ⟨_, hx⟩)
      else
        .inr ⟨x, by rwa [not_lt] at hx⟩
    leftInv x := by
      cases x <;> simp
      · rw [dif_pos]
        congr
        apply f₀.inj
        rw [←hf]
        rw [rank_congr]
        apply rank_lt_type
      · rw [dif_neg]
        rw [not_lt]
        rename_i x
        exact x.property
    rightInv x := by
      simp
      by_cases hx:rank relα x < type relβ
      · rw [dif_pos hx]
        simp
        rw [←hf]
      · rw [dif_neg hx]
    resp_rel := by
      intro x y
      simp
      cases x <;> cases y <;> simp
      apply f₀.resp_rel
      apply rank_lt_rank_iff.mp
      rw [rank_congr]
      apply lt_of_lt_of_le
      apply rank_lt_type
      rename_i x
      apply x.property
      apply rank_le_rank_iff.mp
      rename_i x _
      rw [rank_congr]
      apply le_trans
      apply le_of_lt; apply rank_lt_type
      apply x.property
  }

def add_sub_cancel' (a b: Ordinal) : (b + a) - b = a := by
  classical
  cases a with | _ α relα =>
  cases b with | _ β relβ =>
  apply sound
  simp
  symm
  exact {
    toFun x := {
      val := .inr x
      property := by
        refine ⟨?_⟩
        simp
        exact {
          toFun b := {
            val := Sum.inl b
            property := Sum.Lex.sep _ _
          }
          inj' := by
            intro x y h
            simpa using h
          resp_rel := by
            intro x y
            simp
            simp [rel_rank]
          isInitial := by
            intro a ⟨y, hy⟩
            cases hy
            simp
            nofun
            simp
        }
    }
    invFun
    | ⟨x, hx⟩ =>
      match x with
      | .inl b => by
        rw [←apply_rel_add_of_left, rank_congr] at hx
        rw [←not_lt] at hx
        have := hx (rank_lt_type _)
        contradiction
      | .inr a => a
    leftInv x := rfl
    rightInv x := by
      obtain ⟨x, hx⟩ := x
      simp
      split
      rename_i h
      rw [←apply_rel_add_of_left, rank_congr, ←not_lt] at h
      have := h (rank_lt_type _)
      contradiction
      rfl
    resp_rel := by
      intro a b
      simp
  }

def sub_self (a: Ordinal) : a - a = 0 := by
  apply sub_of_le
  rfl

def add_sub_assoc (a b c: Ordinal) (h: c ≤ a) : (a + b) - c = (a - c) + b := by
  cases a with | _ A rela =>
  cases b with | _ B relb =>
  cases c with | _ C relc =>
  obtain ⟨h⟩ := h
  simp at h
  have : ∀c a, rela a (h c) -> a ∈ Set.range h := h.isInitial
  apply sound
  simp
  exact {
    toFun
    | ⟨.inl x, hx⟩ => .inl {
      val := x
      property := by rwa [←apply_rel_add_of_left, rank_congr] at hx
    }
    | ⟨.inr x, hx⟩ => .inr x
    invFun
    | .inl x => {
      val := .inl x
      property := by
        rw [←apply_rel_add_of_left, rank_congr]
        exact x.property
    }
    | .inr x => {
      val := .inr x
      property := by
        apply le_trans
        show type relc ≤ type rela
        exact ⟨h⟩
        refine ⟨?_⟩
        simp
        exact {
          toFun a := {
            val := .inl a
            property := by simp
          }
          inj' := by
            intro x y h
            cases h
            rfl
          resp_rel := by
            intro a₀ a₁; simp [rel_rank]
          isInitial := by
            intro a ⟨b, hb⟩ h
            simp [rel_rank] at h
            cases h
            apply Set.mem_range'
        }
    }
    leftInv := by
      intro ⟨x, hx⟩
      cases x <;> rfl
    rightInv := by
      intro x
      cases x <;> rfl
    resp_rel := by
      intro ⟨x, hx⟩ ⟨y, hy⟩
      cases x <;> cases y <;> simp
  }

end Sub

section DivMod

noncomputable def modFin (n: ℕ) : Ordinal -> ℕ :=
  transfiniteRecursion' (motive := fun _ => ℕ)
    (fun _ _ _ => 0)
    (fun _ ih => (ih + 1) % n)

noncomputable instance : HMod Ordinal ℕ ℕ where
  hMod o n := modFin n o

def divFin (n: ℕ) : Ordinal -> Ordinal := by
  let f (α: Type _) (relα: α -> α -> Prop) [Relation.IsWellOrder relα] : Ordinal := by
    apply subtype relα (fun x => (rank relα x % n: ℕ) = 0)
  refine lift f ?_
  intro α β relα relβ _ _ h
  apply subtype_congr h
  intro x
  rw [show h x = h.toInitial x from rfl, rank_congr h.toInitial]

noncomputable instance : HDiv Ordinal ℕ Ordinal where
  hDiv o n := divFin n o

def modFin_limit (n: ℕ) (o: Ordinal) [IsLimitOrdinal o] : (o % n: ℕ) = 0 := by
  apply transfiniteRecursion'_limit

def modFin_succ (n: ℕ) (o: Ordinal) : ((o + 1) % n: ℕ) = ((o % n: ℕ) + 1) % n := by
  apply transfiniteRecursion'_succ

noncomputable def parity (o: Ordinal) : Fin 2 :=
  ⟨o % 2, by
    induction o using transfiniteRecursion' with
    | limit o ho =>
      rw [modFin_limit]
      trivial
    | succ o ih =>
      rw [modFin_succ]
      apply Nat.mod_lt
      trivial⟩

def parity_limit (o: Ordinal) [IsLimitOrdinal o] : o.parity = 0 :=
  (Fin.val_inj (a := ⟨_, _⟩) (b := ⟨_, _⟩)).mp (modFin_limit 2 o)

def parity_succ (o: Ordinal) : (o + 1).parity = o.parity + 1 :=
  (Fin.val_inj (a := ⟨_, _⟩) (b := ⟨_, _⟩)).mp (modFin_succ 2 _)

def divFin_add_modFin (n: ℕ) (o: Ordinal) : n * divFin n o + modFin n o = o := by
    sorry

end DivMod

section Basics

instance IsSuccLimitOrdinal.add (a b: Ordinal) [hb: b.IsSuccLimitOrdinal] : IsSuccLimitOrdinal (a + b) where
  ne_succ := by
    intro x hx h
    cases a with | _ α relα =>
    cases b with | _ β relβ =>
    cases x with | _ γ relγ =>
    replace ⟨h⟩ := exact h
    simp at h
    let x := h .none
    match hx:x with
    | .inl a =>
      have : Nonempty β := by
        apply Classical.byContradiction
        intro g
        replace g := IsEmpty.ofNotNonempty g
        apply hb.out
        apply sound
        exact {
          Equiv.empty with
          resp_rel {x} := elim_empty x
        }
      obtain ⟨b⟩ := this
      have : Sum.Lex relα relβ (.inl a) (.inr b) := Sum.Lex.sep _ _
      rw [←hx] at this
      replace this := h.symm.resp_rel.mp this
      simp [x] at this
      nomatch this
    | .inr top =>
      have ⟨b, r⟩ := nomax relβ inferInstance top
      have : Sum.Lex relα relβ (.inr top) (.inr b) := Sum.Lex.inr r
      replace this := h.symm.resp_rel.mp this
      simp at this
      rw [←hx] at this
      simp [x] at this
      nomatch this
  out := by
    intro h
    suffices b = 0 by
      apply hb.out
      assumption
    cases a with | _ α relα =>
    cases b with | _ β relβ =>
    replace ⟨h⟩ := exact h
    simp at h
    have g := (h.toEquiv).trans (Equiv.ulift _)
    apply sound
    simp
    apply RelIso.trans _ h
    clear h
    exact RelIso.symm {
      toFun x := (g x).elim0
      invFun x := (g (.inr x)).elim0
      leftInv x := (g x).elim0
      rightInv x := (g (.inr x)).elim0
      resp_rel {x} := (g x).elim0
    }

def IsLimitOrdinal.add (a b: Ordinal) (ha: a.IsLimitOrdinal ∨ b ≠ 0) (hb: b.IsLimitOrdinal) : IsLimitOrdinal (a + b) := by
  by_cases hb₀:b = 0
  subst b
  simp
  apply ha.resolve_right
  simp
  have : b.IsSuccLimitOrdinal := {hb with out := hb₀}
  infer_instance

instance (a b: Ordinal) [a.IsLimitOrdinal] [b.IsLimitOrdinal] : IsLimitOrdinal (a + b) := by
  apply IsLimitOrdinal.add
  left; assumption
  assumption

instance (a b: Ordinal) [hb₀: NeZero b] [hb: b.IsLimitOrdinal] : IsLimitOrdinal (a + b) := by
  have : b.IsSuccLimitOrdinal := { hb, hb₀ with }
  infer_instance

end Basics

end Ordinal
