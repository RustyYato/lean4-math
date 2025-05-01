import Math.Relation.RelIso
import Math.Tactics.PPWithUniv
import Math.Relation.Segments
import Math.Order.Defs

namespace Ordinal

universe u v w

variable {α β γ δ: Type _}
  (rel: α -> α -> Prop)
  {r: α -> α -> Prop} {s: β -> β -> Prop}
  {t: γ -> γ -> Prop} {u: δ -> δ -> Prop}
  [Relation.IsWellOrder rel]
  [Relation.IsWellOrder r] [Relation.IsWellOrder s]
  [Relation.IsWellOrder t] [Relation.IsWellOrder u]

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

def typein_lt_typein_init_iff (init: r ≼i s) (a: α) (b: β) : typein r a < typein s b ↔ s (init a) b := by
  symm; apply Iff.intro
  · intro h
    exact ⟨{
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
    }⟩
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
      simp; rw [←hf]
    rightInv x := by
      simp; congr; rw [←hf]
    resp_rel := init.resp_rel
  }

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

end Ordinal
