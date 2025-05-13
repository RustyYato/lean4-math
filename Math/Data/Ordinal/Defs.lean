import Math.Relation.RelIso
import Math.Tactics.PPWithUniv
import Math.Relation.Segments
import Math.Order.Defs
import Math.Data.Fin.Pairing
import Math.Order.Lattice.ConditionallyComplete

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

instance pre_setoid : Setoid Pre where
  r a b := Nonempty (a.rel ≃r b.rel)
  iseqv := {
    refl _ := ⟨RelIso.refl⟩
    symm | ⟨h⟩ => ⟨h.symm⟩
    trans | ⟨h⟩, ⟨g⟩ => ⟨h.trans g⟩
  }

@[pp_with_univ]
def _root_.Ordinal := Quotient pre_setoid

def type {α: Type u} (rel: α -> α -> Prop) [Relation.IsWellOrder rel] : Ordinal := Quotient.mk _ (Pre.mk _ rel)

@[cases_eliminator]
def ind {motive : Ordinal -> Prop} (type: ∀(α: Type u) (rel: α -> α -> Prop) [Relation.IsWellOrder rel], motive (type rel)) (o: Ordinal) : motive o := by
  induction o using Quotient.ind with | _ o =>
  apply type

def sound {α β: Type u} (relα: α -> α -> Prop) (relβ: β -> β -> Prop) (hrelα: Relation.IsWellOrder relα := by infer_instance) (hrelβ: Relation.IsWellOrder relβ := by infer_instance) :
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

def le_add_left (a b: Ordinal) : a ≤ a + b := by
  cases a with | _ _ a =>
  cases b with | _ _ b =>
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
  infer_instance
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

inductive maxType where
| common (a: α) (b: β) (h: rank relα a = rank relβ b)
| inl (a: α) (h: ∀b: β, rank relβ b < rank relα a)
| inr (b: β) (h: ∀a: α, rank relα a < rank relβ b)

inductive rel_max : maxType relα relβ -> maxType relα relβ -> Prop where
| inl : relα a₀ a₁ -> rel_max (.inl a₀ h₀) (.inl a₁ h₁)
| inr : relβ b₀ b₁ -> rel_max (.inr b₀ h₀) (.inr b₁ h₁)
| common : relα a₀ a₁ -> rel_max (.common a₀ b₀ h₀) (.common a₁ b₁ h₁)
| common_inl : rel_max (.common a₀ b₀ h₀) (.inl a₁ h₁)
| common_inr : rel_max (.common a₀ b₀ h₀) (.inr b₁ h₁)

namespace maxType

def not_inl_and_inr
  (a: α) (ha: ∀b₀, rank s b₀ < rank r a)
  (b: β) (hb: ∀a₀, rank r a₀ < rank s b): False :=
  lt_asymm (ha b) (hb a)

def acc_common : Acc (rel_max relα relβ) (.common a b h) := by
  induction a using Relation.wfInduction relα generalizing b with
  | h a ih =>
  apply Acc.intro
  intro x hx
  cases hx
  apply ih
  assumption

def acc_inl : Acc (rel_max relα relβ) (.inl a h) := by
  induction a using Relation.wfInduction relα with
  | h a ih =>
  apply Acc.intro
  intro x hx
  cases hx
  apply ih
  assumption
  apply acc_common

def acc_inr : Acc (rel_max relα relβ) (.inr b h) := by
  induction b using Relation.wfInduction relβ with
  | h b ih =>
  apply Acc.intro
  intro x hx
  cases hx
  apply ih
  assumption
  apply acc_common

instance : Relation.IsWellFounded (rel_max relα relβ) where
  wf := by
    apply WellFounded.intro
    intro a; cases a
    apply acc_common
    apply acc_inl
    apply acc_inr

instance : Relation.IsTrans (rel_max relα relβ) where
  trans {a b c} h g := by
    cases h <;> cases g
    apply rel_max.inl
    apply Relation.trans' <;> assumption
    apply rel_max.inr
    apply Relation.trans' <;> assumption
    apply rel_max.common
    apply Relation.trans' <;> assumption
    any_goals apply rel_max.common_inl
    all_goals apply rel_max.common_inr

instance : Relation.IsConnected (rel_max relα relβ) where
  connected_by a b := by
    cases a <;> cases b
    · rename_i a₀ b₀ h₀ a₁ b₁ h₁
      rcases Relation.connected relα a₀ a₁ with h | h | h
      left; apply rel_max.common; assumption
      subst a₁
      right; left; rw [h₀] at h₁; rw [rank_inj.eq_iff] at h₁; congr
      right; right; apply rel_max.common; assumption
    · left; apply rel_max.common_inl
    · left; apply rel_max.common_inr
    · right; right; apply rel_max.common_inl
    · rename_i a₀ h₀ a₁ h₁
      rcases Relation.connected relα a₀ a₁ with h | h | h
      left; apply rel_max.inl; assumption
      subst a₁
      right; left; rfl
      right; right; apply rel_max.inl; assumption
    · rename_i b hb a ha
      exfalso; apply not_inl_and_inr _ ha _ hb
    · right; right; apply rel_max.common_inr
    · rename_i b₀ hb a ha
      exfalso; apply not_inl_and_inr _ ha _ hb
    · rename_i b₀ h₀ b₁ h₁
      rcases Relation.connected relβ b₀ b₁ with h | h | h
      left; apply rel_max.inr; assumption
      subst b₁
      right; left; rfl
      right; right; apply rel_max.inr; assumption

instance : Relation.IsWellOrder (rel_max relα relβ) where

def map (ac: r ≃r t) (bd: s ≃r u) : maxType r s -> maxType t u
| .inl a ha => .inl (ac a) <| by
  intro d
  erw [rank_congr ac.toInitial]
  rw [←bd.symm_coe d]
  erw [rank_congr bd.toInitial]
  apply ha
| .inr b hb => .inr (bd b) <| by
  intro c
  erw [rank_congr bd.toInitial]
  rw [←ac.symm_coe c]
  erw [rank_congr ac.toInitial]
  apply hb
| .common a b h => .common (ac a) (bd b) <| by
  erw [rank_congr ac.toInitial, rank_congr bd.toInitial]
  assumption

def swap : maxType r s -> maxType s r
| .inl a ha => .inr a ha
| .inr b hb => .inl b hb
| .common a b h => .common b a h.symm

end maxType

private def rel_max_hom (ac: r ≃r t) (bd: s ≃r u) : rel_max r s →r rel_max t u where
  toFun x := x.map ac bd
  resp_rel {a b} h := by
    cases h
    apply rel_max.inl
    apply ac.resp_rel.mp; assumption
    apply rel_max.inr
    apply bd.resp_rel.mp; assumption
    apply rel_max.common
    apply ac.resp_rel.mp; assumption
    apply rel_max.common_inl
    apply rel_max.common_inr

private def rel_max_swap_hom : rel_max r s →r rel_max s r where
  toFun := maxType.swap
  resp_rel {a b} h := by
    cases h
    apply rel_max.inr
    assumption
    apply rel_max.inl
    assumption
    apply rel_max.common
    rename_i a₀ a₁ b₀ h₀ b₁ h₁ h₂
    have : rel_min r s ⟨(a₀, b₀), h₀⟩ ⟨(a₁, b₁), h₁⟩ := h₂
    rwa [rel_min_eq_rel_min'] at this
    apply rel_max.common_inr
    apply rel_max.common_inl

@[simp]
private def rel_max_hom_symm_coe (ac: r ≃r t) (bd: s ≃r u) : rel_max_hom ac.symm bd.symm (rel_max_hom ac bd x) = x := by
  show (maxType.map _ _ _).map _ _ = _
  cases x
  all_goals
    unfold maxType.map
    simp

def max : Ordinal -> Ordinal -> Ordinal := by
  refine lift₂ (fun _ _ a b _ _ => type (rel_max a b)) ?_
  intro A B C D rela relb relc reld _ _ _ _ ac bd
  simp; apply sound
  exact {
    toFun := rel_max_hom ac bd
    invFun := rel_max_hom ac.symm bd.symm
    leftInv x := by apply rel_max_hom_symm_coe
    rightInv x := by apply rel_max_hom_symm_coe
    resp_rel := by
      intro a b
      apply Iff.intro
      apply (rel_max_hom _ _).resp_rel
      intro h
      have := (rel_max_hom ac.symm bd.symm).resp_rel h
      simpa using this
  }

def exists_rank_eq_of_exists_rank_le (a: α) : (∃b: β, ¬rank s b < rank r a) -> ∃b: β, rank r a = rank s b := by
  intro hb
  have hb := Relation.exists_min s hb
  obtain ⟨b, hb, bmin⟩ := hb
  simp at bmin
  rcases lt_trichotomy (rank s b) (rank r a) with h | h | h
  contradiction
  clear hb
  exists b
  symm; assumption
  have ⟨b', eq⟩ := rank_surj _ _ h
  rw [rank_rel_rank] at eq
  rw [eq] at h
  have := bmin b' (by rwa [rank_lt_rank_iff] at h)
  rw [eq] at this
  have := lt_asymm this
  contradiction

protected def le_max_left (a b: Ordinal) : a ≤ max a b := by
    classical
    cases a with | _ A rela =>
    cases b with | _ B relb =>
    -- if there exists an `a` which is larger than all `B`s
    by_cases h:∃a: A, ∀b: B, rank relb b < rank rela a
    · replace h := Relation.exists_min rela h
      obtain ⟨a₀, ha₀, a₀_min⟩ := h
      simp at a₀_min
      replace a₀_min (a': { a: A // rela a a₀ }) : ∃b: B, rank rela a'.val = rank relb b :=
        exists_rank_eq_of_exists_rank_le _ (a₀_min a'.val a'.property)
      replace a₀_min := Classical.axiomOfChoice a₀_min
      obtain ⟨f, hf⟩ := a₀_min
      simp at hf
      refine ⟨?_⟩
      dsimp; exact {
        toFun a :=
          if ha:rela a a₀ then
            .common a (f ⟨a, ha⟩) (hf _ _)
          else
            .inl a <| by
              intro b
              apply lt_of_lt_of_le
              apply ha₀
              rwa [←rank_le_rank_iff] at ha
        inj' := by
          intro x y h
          simp at h
          split at h <;> split at h
          exact (maxType.common.inj h).left
          contradiction
          contradiction
          exact maxType.inl.inj h
        resp_rel := by
          intro x y
          simp
          split <;> split
          · apply Iff.intro
            intro h; apply rel_max.common
            assumption
            intro h; cases h
            assumption
          · apply Iff.intro
            intro h; apply rel_max.common_inl
            intro; rename_i h' _ _
            rcases Relation.connected rela y a₀ with h | h | h
            contradiction
            subst y; assumption
            exact trans h' h
          · apply Iff.intro
            intro h
            rename_i h' g
            have := trans h g
            contradiction
            nofun
          · apply Iff.intro
            intro h
            apply rel_max.inl
            assumption
            intro h; cases h
            assumption
        isInitial := by
          intro a b h
          replace h : rel_max rela relb b (if _:_ then _ else _) := h
          split at h
          cases h; rename_i h₀ a' b' eq h₁ h₂
          rw [Set.mem_range]
          refine ⟨a', ?_⟩
          show _ = if _:_ then _ else _
          rw[ dif_pos (trans h₁ h₀)]
          congr
          have := hf a' (trans h₁ h₀)
          rw [eq] at this
          exact rank_inj this
          cases h
          rename_i h₀ a' h₁ h₂ h₃
          exists a'
          show _ = if _:_ then _ else _
          rw [dif_neg]
          intro h
          have := h₁ (f ⟨a', h⟩)
          rw [hf a' h] at this
          exact lt_irrefl this
          rename_i h₀ a' b h₁ h₂
          exists a'
          show _ = if _:_ then _ else _
          rw [dif_pos (by have := ha₀ b; rwa [←h₁, rank_lt_rank_iff] at this)]
          congr
          apply rank_inj (r := relb)
          rw (occs := [1]) [←h₁]
          apply hf
      }
    · simp at h
      replace h (a': A) : ∃b: B, rank rela a' = rank relb b :=
        exists_rank_eq_of_exists_rank_le _ (h a')
      replace h := Classical.axiomOfChoice h
      obtain ⟨f, hf⟩ := h
      refine ⟨?_⟩
      simp
      exact {
        toFun a := .common a (f a) (hf a)
        inj' := by
          intro x y h
          simp at h
          exact h.left
        resp_rel := by
          intro x y
          apply Iff.intro
          apply rel_max.common
          intro h; cases h; assumption
        isInitial := by
          intro a b h
          cases h
          rename_i a' b h₀ h₁ h₂
          exists a'
          congr
          symm; rwa [hf, rank_inj.eq_iff] at h₀
      }

protected def max_comm (a b: Ordinal) : max a b = max b a := by
  cases a with | _ A rela =>
  cases b with | _ B relb =>
  apply sound
  infer_instance
  infer_instance
  simp
  refine {
    toFun := maxType.swap
    invFun := maxType.swap
    leftInv x := by cases x <;> rfl
    rightInv x := by cases x <;> rfl
    resp_rel := ?_
  }
  intro x y
  apply Iff.intro
  apply rel_max_swap_hom.resp_rel
  cases x <;> cases y <;> apply rel_max_swap_hom.resp_rel

instance : Max Ordinal where
  max := max

instance : IsSemiLatticeMax Ordinal where
  le_max_left a b := by apply Ordinal.le_max_left
  le_max_right a b := by
    show b ≤ max a b
    rw [Ordinal.max_comm]
    apply Ordinal.le_max_left
  max_le := by
    classical
    suffices ∀a b k: Ordinal, a ≤ b -> b ≤ k -> a ⊔ b ≤ k by
      intro a b k ak bk
      cases le_total a b
      apply this
      assumption
      assumption
      show max _ _ ≤ _; rw [Ordinal.max_comm]
      apply this
      assumption
      assumption
    intro a b k
    cases a with | _ A rela =>
    cases b with | _ B relb =>
    cases k with | _ K relk =>
    intro ⟨ab⟩ ⟨bk⟩
    simp at ab bk
    refine ⟨?_⟩
    simp
    let ak := ab.trans bk
    refine {
      toFun
      | .inl a ha => ak a
      | .inr b hb => bk b
      | .common a b h => ak a
      inj' := ?_
      resp_rel := ?_
      isInitial := ?_
    }
    · intro x y h
      cases x <;> cases y <;> dsimp at h
      · rename_i a₀ b₀ h₀ a₁ b₁ h₁
        cases ak.inj h
        rw [h₀] at h₁
        cases rank_inj h₁
        rfl
      · rename_i a₀ b₀ h₀ a₁ h₁
        have := h₁ b₀
        rw [←h₀] at this
        cases ak.inj h
        have := lt_irrefl this
        contradiction
      · rename_i a₀ b₀ h₀ b₁ h₁
        have := h₁ a₀
        rw [←rank_congr ak, ←rank_congr bk, h] at this
        have := lt_irrefl this
        contradiction
      · rename_i a₁ h₁ a₀ b₀ h₀
        have := h₁ b₀
        rw [←rank_congr ak, ←h₀, ←rank_congr ak, h] at this
        have := lt_irrefl this
        contradiction
      · rename_i h
        cases ak.inj h
        rfl
      · exfalso
        rename_i a ha b hb
        exact maxType.not_inl_and_inr a ha b hb
      · rename_i b₁ h₁ a₀ b₀ h₀
        have := h₁ a₀
        rw [←rank_congr ak, ←rank_congr bk, h] at this
        have := lt_irrefl this
        contradiction
      · exfalso
        rename_i a ha b hb
        exact maxType.not_inl_and_inr b hb a ha
      · rename_i h
        cases bk.inj h
        rfl
    · intro a b
      cases a <;> cases b <;> simp
      · erw [ak.resp_rel.symm]
        apply Iff.intro
        intro h; cases h; assumption
        apply rel_max.common
      · erw [ak.resp_rel.symm]
        apply Iff.intro
        intro h; clear h
        rename_i a₀ b₀ h₀ a₁ h₁
        have := h₁ b₀; rw [←h₀] at this
        rwa [rank_lt_rank_iff] at this
        intro; apply rel_max.common_inl
      · show _ ↔ relk (bk (ab _)) _
        erw [bk.resp_rel.symm]
        rename_i a₀ b₀ h₀ b₁ h₁
        apply Iff.intro
        intro h
        clear h
        rw [←rank_lt_rank_init_iff ab]
        apply h₁
        intro; apply rel_max.common_inr
      · erw [ak.resp_rel.symm]
        rename_i a₁ ha a₀ b₀ h
        apply Iff.intro nofun
        intro g
        rw [←rank_lt_rank_iff (r := rela), h] at g
        have := lt_asymm (ha b₀)
        contradiction
      · erw [ak.resp_rel.symm]
        apply Iff.intro
        intro h; cases h; assumption
        apply rel_max.inl
      · rename_i a ha b hb
        have := maxType.not_inl_and_inr a ha b hb
        contradiction
      · erw [bk.resp_rel.symm]
        rename_i b₁ hb a₀ b₀ h
        apply Iff.intro nofun
        intro g
        rw [←rank_lt_rank_iff (r := relb)] at g
        simp at g
        rw [rank_congr ab] at g
        have := lt_asymm (hb a₀)
        contradiction
      · rename_i a ha b hb
        have := maxType.not_inl_and_inr a ha b hb
        contradiction
      · erw [bk.resp_rel.symm]
        apply Iff.intro
        intro h; cases h; assumption
        apply rel_max.inr
    · intro x k
      cases x <;> simp
      · intro lt; rename_i a b h
        obtain ⟨a', rfl⟩ := ak.isInitial _ _ lt
        simp at *
        erw [ak.resp_rel.symm, ←rank_lt_rank_iff (r := rela)] at lt
        rw [h] at lt
        have ⟨b', hb⟩ := exists_rank_eq_of_exists_rank_le (r := rela) (s := relb) a'
          ⟨b, by
            apply lt_asymm
            assumption⟩
        obtain ⟨lt⟩ := lt
        simp at lt
        exact ⟨.common a' b' hb, rfl⟩
      · rename_i a ha
        intro h
        obtain ⟨a', rfl⟩ := ak.isInitial _ _ h
        simp at *
        refine if ha':rank rela a' < type relb then ?_ else ?_
        have ⟨b', hb'⟩ := rank_surj _ _ ha'
        exists .common a' b' hb'
        refine ⟨.inl a' ?_, rfl⟩
        intro b
        apply lt_of_lt_of_le
        apply rank_lt_type
        rwa [not_lt] at ha'
      · rename_i a ha
        intro h
        obtain ⟨b', rfl⟩ := bk.isInitial _ _ h
        simp at *
        refine if hb':rank relb b' < type rela then ?_ else ?_
        have ⟨a', ha'⟩ := rank_surj _ _ hb'
        exists .common a' b' ha'.symm
        simp
        apply rank_inj (r := relk)
        rwa [rank_congr, rank_congr]
        refine ⟨.inr b' ?_, rfl⟩
        intro b
        apply lt_of_lt_of_le
        apply rank_lt_type
        rwa [not_lt] at hb'

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
  infer_instance
  infer_instance
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
  infer_instance
  infer_instance
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
  infer_instance
  infer_instance
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
  infer_instance
  infer_instance
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
  infer_instance
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
  infer_instance
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
  infer_instance
  infer_instance
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
  infer_instance
  infer_instance
  simp
  apply RelIso.trans _ (rel_ulift_eqv _).symm
  apply RelIso.trans
  apply RelIso.congrSumLex
  apply rel_ulift_eqv
  apply rel_ulift_eqv
  rfl

def ulift_natCast (n: ℕ) : ulift.{v, u} n = n := by
  apply sound
  infer_instance
  infer_instance
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
    inj' a b h := ab.inj (Option.get_inj _ _ _ _ h)
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

def le_iff_add_left {k a b: Ordinal} : a ≤ b ↔ k + a ≤ k + b := by
  apply (add_left_strict_mono k).le_iff_le.symm

def lt_iff_add_left {k a b: Ordinal} : a < b ↔ k + a < k + b := by
  apply (add_left_strict_mono k).lt_iff_lt.symm

def addLeft (a: Ordinal) : Ordinal ↪o Ordinal where
  toFun x := a + x
  inj' := (add_left_strict_mono a).Injective
  map_le _ _ := le_iff_add_left

end Nat

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

noncomputable def transfiniteRecursion'
  {motive : Ordinal -> Sort*}
  (limit: ∀o, IsLimitOrdinal o -> (∀x < o, motive x) -> motive o)
  (succ: ∀o, motive o -> motive (o + 1)) (o: Ordinal) : motive o :=
  open scoped Classical in
  if h:∃x, x + 1 = o then
    let x := Classical.choose h
    have hx : x + 1 = o := Classical.choose_spec h
    cast (by rw [hx]) (succ x (transfiniteRecursion' limit succ x))
  else
    limit _ { ne_succ x hx g := by exact h ⟨_, succ_eq_add_one _ ▸ g⟩} (fun x hx => transfiniteRecursion' limit succ x)
termination_by o
decreasing_by
  · show x < o
    rw [←hx]
    apply lt_succ_self
  · assumption

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
  unfold transfiniteRecursion transfiniteRecursion'
  simp; intro x h
  have := limit_ne_succ 0 _ h
  contradiction

def transfiniteRecursion_limit (o: Ordinal) [IsSuccLimitOrdinal o] : transfiniteRecursion zero succ limit o = limit o inferInstance (fun x _ => transfiniteRecursion zero succ limit x) := by
  rw [transfiniteRecursion, transfiniteRecursion']
  simp; rw [dif_neg, dif_neg]
  rfl
  rename_i h; exact h.out
  rename_i h; simp; exact limit_ne_succ o

def transfiniteRecursion_succ (o: Ordinal) : transfiniteRecursion zero succ limit (o + 1) = succ o (transfiniteRecursion zero succ limit o) := by
  rw [transfiniteRecursion, transfiniteRecursion']
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

end Ordinal
