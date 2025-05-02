import Math.Relation.RelIso
import Math.Tactics.PPWithUniv
import Math.Relation.Segments
import Math.Order.Defs

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
def type' {α: Type u} (rel: α -> α -> Prop) (is_well_order: Relation.IsWellOrder rel) : Ordinal := type rel

@[induction_eliminator]
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

def rel_ulift : Relation (ULift α) := fun a b => rel a.down b.down
def rel_ulift_hom : rel_ulift rel ↪r rel where
  toFun x := x.down
  resp_rel := Iff.rfl
  inj' := (Equiv.ulift _).inj

instance : Relation.IsWellOrder (rel_ulift rel) := (rel_ulift_hom rel).lift_wo

def ulift : Ordinal.{u} -> Ordinal.{max u v} := by
  refine lift (fun α relα _ => Ordinal.type' (rel_ulift relα) ?_) ?_
  · exact (rel_ulift_hom relα).lift_wo
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
    induction a with | _ α rel =>
    exact ⟨InitialSegment.refl _⟩
  le_trans {a b c} h g := by
    induction a with | _ a rela =>
    induction b with | _ b relb =>
    induction c with | _ c relc =>
    obtain ⟨h⟩ := h
    obtain ⟨g⟩ := g
    dsimp at h g
    exact ⟨h.trans g⟩
  le_antisymm {a b} h g := by
    induction a with | _ a rela =>
    induction b with | _ b relb =>
    obtain ⟨h⟩ := h
    obtain ⟨g⟩ := g
    dsimp at h g
    apply sound
    exact InitialSegment.antisymm h g
  lt_iff_le_and_not_le {a b} := by
    induction a with | _ a rela =>
    induction b with | _ b relb =>
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
  mul := add

def rel_typein (top: α) : Relation { x: α // rel x top } := fun a b => rel a b
def rel_typein_emb (top: α) : rel_typein rel top ↪r rel where
  toFun x := x.val
  inj' := Subtype.val_inj
  resp_rel := Iff.rfl
def rel_typein_princ_top (top: α) : (rel_typein_emb rel top).IsPrincipalTop top := by
  intro x
  apply Iff.intro
  intro h
  exists ⟨x, h⟩
  rintro ⟨x, rfl⟩
  exact x.property
def rel_typein_hom (top: α) : rel_typein rel top ≺i rel where
  toRelEmbedding := rel_typein_emb rel top
  exists_top := by exists top; apply rel_typein_princ_top

instance : Relation.IsWellOrder (rel_typein rel top) :=
  (rel_typein_hom rel top).toRelEmbedding.lift_wo

def typein (top: α) := Ordinal.type (rel_typein rel top)
def typein' (rel: α -> α -> Prop) (h: Relation.IsWellOrder rel) (top: α) := typein rel top

def typein_surj : ∀o < type rel, ∃top, o = typein rel top := by
  intro o ho
  induction o with | _ β relβ =>
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

def typein_lt_type (top: α) : typein r top < type r := ⟨rel_typein_hom r top⟩

def rel_typein_lt_rel_typein_init (init: r ≼i s) (a: α) (b: β) (h: s (init a) b) : rel_typein r a ≺i rel_typein s b where
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

def rel_typein_rel_typein (a top: α) (h: r top a) : rel_typein (rel_typein r a) ⟨top, h⟩ ≃r rel_typein r top where
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

def typein_lt_typein_init_iff (init: r ≼i s) (a: α) (b: β) : typein r a < typein s b ↔ s (init a) b := by
  symm; apply Iff.intro
  · intro h
    exact ⟨rel_typein_lt_rel_typein_init init a b h⟩
  · intro ⟨h⟩
    dsimp at h

    let r₀ := h.trans (rel_typein_hom s b)
    let r₁ := (rel_typein_hom r a).lt_of_lt_of_le init
    have eq : r₁ = r₀ := Subsingleton.allEq _ _
    have princ_top: r₁.IsPrincipalTop (init a) := by
      apply PrincipalSegment.top_of_lt_of_lt_of_le
      apply rel_typein_princ_top
    rw [eq] at princ_top
    have ⟨top, htop⟩ := h.exists_top
    have top' : r₀.IsPrincipalTop top := by
      apply PrincipalSegment.top_of_lt_of_lt_of_le
      assumption
    rw [PrincipalSegment.top_unique' _ _ _ princ_top top']
    exact top.property

def typein_lt_typein_iff {a b: α} : typein r a < typein r b ↔ r a b := typein_lt_typein_init_iff (InitialSegment.refl _) _ _

def typein_congr (init: r ≼i s) (top: α) : typein s (init top) = typein r top := by
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

def typein_typein (a top: α) (h: r top a) : typein (rel_typein r a) ⟨top, h⟩ = typein r top := by
  apply sound
  apply rel_typein_rel_typein

def typein_inj_initial (init: r ≼i s) (a: α) (b: β) : typein r a = typein s b -> b = init a := by
  intro h
  apply Relation.eq_of_not_lt_or_gt s
  intro g
  obtain ⟨b, rfl⟩ := init.isInitial _ _ g
  simp at *
  rw [←typein_lt_typein_init_iff init, typein_congr, h, typein_congr] at g
  exact lt_irrefl g
  intro g
  rw [←typein_lt_typein_init_iff init, h] at g
  exact lt_irrefl g

def typein_inj : Function.Injective (typein r) := by intro x y h; apply typein_inj_initial (InitialSegment.refl r) _ _ h.symm

instance : @Relation.IsWellFounded Ordinal (· < ·) where
  wf := by
    apply WellFounded.intro
    intro a
    apply Acc.intro
    intro b r
    induction a using ind with | _ _ rel =>
    have ⟨a₀, eq⟩ := typein_surj rel b r
    subst b
    clear r
    induction a₀ using (Relation.wellFounded rel).induction with
    | h a₀ ih =>
    apply Acc.intro
    intro c r
    have ⟨c₀, eq⟩ := typein_surj _ _ (lt_trans r (typein_lt_type _))
    subst eq
    apply ih
    apply typein_lt_typein_iff.mp r

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
  induction o with | _ _ rel =>
  have ⟨a, eq⟩ := typein_surj _ a ao
  subst eq
  have ⟨b, eq⟩ := typein_surj _ b bo
  subst eq
  rcases Relation.connected rel a b with ab | eq | ba
  left; apply le_of_lt; apply typein_lt_typein_iff.mpr; assumption
  left; rw [eq]
  right; apply le_of_lt; apply typein_lt_typein_iff.mpr; assumption

def le_add_left (a b: Ordinal) : a ≤ a + b := by
  induction a with | _ _ a =>
  induction b with | _ _ b =>
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
  induction a with | _ _ a =>
  induction b with | _ _ b =>
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

def typein_le_typein_iff {a b: α} : typein r a ≤ typein r b ↔ ¬r b a := by
  rw [←not_lt]
  apply Iff.not_iff_not
  apply typein_lt_typein_iff

end Defs

section Lattice

-- the minimum of two relations is the relation on pairs of elements which
-- are in the same position as each other in their respective orders
-- since this puts elements in 1-1 correspondence, there can't be elements
-- than the smaller of the two relations
def minType := { x: α × β // Ordinal.typein relα x.fst = Ordinal.typein relβ x.snd }

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
      cases typein_inj hy
      have := Relation.irrefl h
      contradiction
    · rw [←typein_lt_typein_iff (r := relβ)] at hβ
      rw [←hx, ←hy] at hβ
      rw [typein_lt_typein_iff] at hβ
      have := Relation.asymm h hβ
      contradiction
  · intro h
    rcases Relation.connected relα x₀ y₀ with hα | hα | hα
    assumption
    · subst y₀
      rw [hx] at hy
      cases typein_inj hy
      have := Relation.irrefl h
      contradiction
    · rw [←typein_lt_typein_iff (r := relα)] at hα
      rw [hx, hy] at hα
      rw [typein_lt_typein_iff] at hα
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
    rwa [hx, typein_inj.eq_iff] at hy
  resp_rel := Iff.rfl
  isInitial := by
    intro ⟨⟨x₀, x₁⟩, hx⟩ a
    show relα a x₀ -> _
    intro h
    suffices ∃b, typein relα a = typein relβ b by
      obtain ⟨b, eq⟩ := this
      exists ⟨⟨_, _⟩, eq⟩
    have ⟨ltα⟩ := typein_lt_type (r := relα) x₀
    have ⟨ltβ⟩ := typein_lt_type (r := relβ) x₁
    replace ⟨hx⟩ := Quotient.exact hx
    let ha := rel_typein_lt_rel_typein_init (InitialSegment.refl relα) a x₀ h
    let b := hx ⟨a, h⟩
    have htop := PrincipalSegment.top_of_lt_of_lt_of_le ha (InitialSegment.ofRelIso hx) ⟨_, h⟩ <| by
      intro ⟨x, hx⟩
      simp
      show relα x a ↔ _
      apply Iff.intro
      · intro x_lt_a
        refine ⟨⟨_, x_lt_a⟩, ?_⟩
        rfl
      · intro ⟨⟨_, _⟩, rfl⟩
        assumption
    exists b
    rw [←typein_typein (r := relα) _ _ h, ←typein_typein (r := relβ)]
    symm; apply typein_congr (InitialSegment.ofRelIso hx)

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
    rw [←typein_congr (InitialSegment.ofRelIso ac) a, ←typein_congr (InitialSegment.ofRelIso bd) b]
    rfl
  · simp
    intro ⟨⟨a, b⟩, h₀⟩ ⟨⟨c, d⟩, h₁⟩
    apply ac.resp_rel

def min_le_left' (a b: Ordinal) : min a b ≤ a := by
  induction a with | _ _ a =>
  induction b with | _ _ b =>
  exact ⟨rel_min_hom_left _ _⟩
def min_le_right' (a b: Ordinal) : min a b ≤ b := by
  induction a with | _ _ a =>
  induction b with | _ _ b =>
  exact ⟨rel_min_hom_right _ _⟩

instance : Min Ordinal where
  min := min

instance : IsLawfulMin Ordinal where
  min_le_left := min_le_left'
  min_le_right := min_le_right'

instance : IsSemiLatticeMin Ordinal where
  le_min := by
    intro a b k ka kb
    induction a with | _ A rela =>
    induction b with | _ B relb =>
    induction k with | _ K relk =>
    obtain ⟨ka⟩ := ka
    obtain ⟨kb⟩ := kb
    refine ⟨?_⟩
    simp; simp at ka kb
    exact {
      toFun k := {
        val := (ka k, kb k)
        property := by
          simp;
          rw [typein_congr, typein_congr]
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
        rw [typein_congr ka, ←typein_congr kb] at h
        symm; exact typein_inj h
    }

inductive maxType where
| common (a: α) (b: β) (h: typein relα a = typein relβ b)
| inl (a: α) (h: ∀b: β, typein relβ b < Ordinal.typein relα a)
| inr (b: β) (h: ∀a: α, typein relα a < Ordinal.typein relβ b)

inductive rel_max : maxType relα relβ -> maxType relα relβ -> Prop where
| inl : relα a₀ a₁ -> rel_max (.inl a₀ h₀) (.inl a₁ h₁)
| inr : relβ b₀ b₁ -> rel_max (.inr b₀ h₀) (.inr b₁ h₁)
| common : relα a₀ a₁ -> rel_max (.common a₀ b₀ h₀) (.common a₁ b₁ h₁)
| common_inl : rel_max (.common a₀ b₀ h₀) (.inl a₁ h₁)
| common_inr : rel_max (.common a₀ b₀ h₀) (.inr b₁ h₁)

namespace maxType

def not_inl_and_inr
  (a: α) (ha: ∀b₀, Ordinal.typein s b₀ < Ordinal.typein r a)
  (b: β) (hb: ∀a₀, Ordinal.typein r a₀ < Ordinal.typein s b): False :=
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
      right; left; rw [h₀] at h₁; rw [typein_inj.eq_iff] at h₁; congr
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
  erw [typein_congr ac.toInitial]
  rw [←bd.symm_coe d]
  erw [typein_congr bd.toInitial]
  apply ha
| .inr b hb => .inr (bd b) <| by
  intro c
  erw [typein_congr bd.toInitial]
  rw [←ac.symm_coe c]
  erw [typein_congr ac.toInitial]
  apply hb
| .common a b h => .common (ac a) (bd b) <| by
  erw [typein_congr ac.toInitial, typein_congr bd.toInitial]
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

def exists_typein_eq_of_exists_typein_le (a: α) : (∃b: β, ¬typein s b < typein r a) -> ∃b: β, typein r a = typein s b := by
  intro hb
  have hb := Relation.exists_min s hb
  obtain ⟨b, hb, bmin⟩ := hb
  simp at bmin
  rcases lt_trichotomy (typein s b) (typein r a) with h | h | h
  contradiction
  clear hb
  exists b
  symm; assumption
  have ⟨b', eq⟩ := typein_surj _ _ h
  rw [typein_typein] at eq
  rw [eq] at h
  have := bmin b' (by rwa [typein_lt_typein_iff] at h)
  rw [eq] at this
  have := lt_asymm this
  contradiction

protected def le_max_left (a b: Ordinal) : a ≤ max a b := by
    classical
    induction a with | _ A rela =>
    induction b with | _ B relb =>
    -- if there exists an `a` which is larger than all `B`s
    by_cases h:∃a: A, ∀b: B, typein relb b < typein rela a
    · replace h := Relation.exists_min rela h
      obtain ⟨a₀, ha₀, a₀_min⟩ := h
      simp at a₀_min
      replace a₀_min (a': { a: A // rela a a₀ }) : ∃b: B, typein rela a'.val = typein relb b :=
        exists_typein_eq_of_exists_typein_le _ (a₀_min a'.val a'.property)
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
              rwa [←typein_le_typein_iff] at ha
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
          exact typein_inj this
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
          rw [dif_pos (by have := ha₀ b; rwa [←h₁, typein_lt_typein_iff] at this)]
          congr
          apply typein_inj (r := relb)
          rw (occs := [1]) [←h₁]
          apply hf
      }
    · simp at h
      replace h (a': A) : ∃b: B, typein rela a' = typein relb b :=
        exists_typein_eq_of_exists_typein_le _ (h a')
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
          symm; rwa [hf, typein_inj.eq_iff] at h₀
      }

protected def max_comm (a b: Ordinal) : max a b = max b a := by
  induction a with | _ A rela =>
  induction b with | _ B relb =>
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
    induction a with | _ A rela =>
    induction b with | _ B relb =>
    induction k with | _ K relk =>
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
        cases typein_inj h₁
        rfl
      · rename_i a₀ b₀ h₀ a₁ h₁
        have := h₁ b₀
        rw [←h₀] at this
        cases ak.inj h
        have := lt_irrefl this
        contradiction
      · rename_i a₀ b₀ h₀ b₁ h₁
        have := h₁ a₀
        rw [←typein_congr ak, ←typein_congr bk, h] at this
        have := lt_irrefl this
        contradiction
      · rename_i a₁ h₁ a₀ b₀ h₀
        have := h₁ b₀
        rw [←typein_congr ak, ←h₀, ←typein_congr ak, h] at this
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
        rw [←typein_congr ak, ←typein_congr bk, h] at this
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
        rwa [typein_lt_typein_iff] at this
        intro; apply rel_max.common_inl
      · show _ ↔ relk (bk (ab _)) _
        erw [bk.resp_rel.symm]
        rename_i a₀ b₀ h₀ b₁ h₁
        apply Iff.intro
        intro h
        clear h
        rw [←typein_lt_typein_init_iff ab]
        apply h₁
        intro; apply rel_max.common_inr
      · erw [ak.resp_rel.symm]
        rename_i a₁ ha a₀ b₀ h
        apply Iff.intro nofun
        intro g
        rw [←typein_lt_typein_iff (r := rela), h] at g
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
        rw [←typein_lt_typein_iff (r := relb)] at g
        simp at g
        rw [typein_congr ab] at g
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
        erw [ak.resp_rel.symm, ←typein_lt_typein_iff (r := rela)] at lt
        rw [h] at lt
        have ⟨b', hb⟩ := exists_typein_eq_of_exists_typein_le (r := rela) (s := relb) a'
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
        refine if ha':typein rela a' < type relb then ?_ else ?_
        have ⟨b', hb'⟩ := typein_surj _ _ ha'
        exists .common a' b' hb'
        refine ⟨.inl a' ?_, rfl⟩
        intro b
        apply lt_of_lt_of_le
        apply typein_lt_type
        rwa [not_lt] at ha'
      · rename_i a ha
        intro h
        obtain ⟨b', rfl⟩ := bk.isInitial _ _ h
        simp at *
        refine if hb':typein relb b' < type rela then ?_ else ?_
        have ⟨a', ha'⟩ := typein_surj _ _ hb'
        exists .common a' b' ha'.symm
        simp
        apply typein_inj (r := relk)
        rwa [typein_congr, typein_congr]
        refine ⟨.inr b' ?_, rfl⟩
        intro b
        apply lt_of_lt_of_le
        apply typein_lt_type
        rwa [not_lt] at hb'

instance : IsLinearLattice Ordinal where

end Lattice

end Ordinal
