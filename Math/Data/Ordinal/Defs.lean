import Math.Relation.RelIso
import Math.Tactics.PPWithUniv
import Math.Relation.Segments
import Math.Order.Defs

namespace Ordinal

universe u v w

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

def lift (f: ∀(α: Type u) (relα: α -> α -> Prop) [Relation.IsWellOrder relα], γ) (hf: ∀(α β: Type u) (relα: α -> α -> Prop) (relβ: β -> β -> Prop) [Relation.IsWellOrder relα] [Relation.IsWellOrder relβ], relα ≃r relβ -> f α relα = f β relβ) : Ordinal -> γ := by
  refine Quotient.lift (fun p => f p.ty p.rel) ?_
  intro a b ⟨h⟩; apply hf
  assumption

def lift₂ (f: ∀(α: Type u) (β: Type v) (relα: α -> α -> Prop) (relβ: β -> β -> Prop) [Relation.IsWellOrder relα] [Relation.IsWellOrder relβ], γ)
  (hf: ∀(α β γ δ)
    (relα: α -> α -> Prop) (relβ: β -> β -> Prop)
    (relγ: γ -> γ -> Prop) (relδ: δ -> δ -> Prop)
    [Relation.IsWellOrder relα] [Relation.IsWellOrder relβ]
    [Relation.IsWellOrder relγ] [Relation.IsWellOrder relδ],
    relα ≃r relγ ->
    relβ ≃r relδ -> f α β relα relβ = f γ δ relγ relδ) : Ordinal -> Ordinal -> γ := by
  refine Quotient.lift₂ (fun p q => f _ _ p.rel q.rel) ?_
  intro a b c d ⟨h⟩ ⟨g⟩; apply hf
  assumption
  assumption

def rel_ulift {α: Type u} (rel: α -> α -> Prop) : Relation (ULift α) := fun a b => rel a.down b.down
def rel_ulift_hom {α: Type u} (rel: α -> α -> Prop) : rel_ulift rel ↪r rel where
  toFun x := x.down
  resp_rel := Iff.rfl
  inj' := (Equiv.ulift _).inj

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

def rel_typein {α: Type u} (rel: α -> α -> Prop) (top: α) : Relation { x: α // rel x top } := fun a b => rel a b
def rel_typein_emb {α: Type u} (rel: α -> α -> Prop) (top: α) : rel_typein rel top ↪r rel where
  toFun x := x.val
  inj' := Subtype.val_inj
  resp_rel := Iff.rfl
def rel_typein_princ_top {α: Type u} (rel: α -> α -> Prop) (top: α) : (rel_typein_emb rel top).IsPrincipalTop top := by
  intro x
  apply Iff.intro
  intro h
  exists ⟨x, h⟩
  rintro ⟨x, rfl⟩
  exact x.property
def rel_typein_hom {α: Type u} (rel: α -> α -> Prop) (top: α) : rel_typein rel top ≺i rel where
  toRelEmbedding := rel_typein_emb rel top
  exists_top := by exists top; apply rel_typein_princ_top

instance [Relation.IsWellOrder rel] : Relation.IsWellOrder (rel_typein rel top) :=
  (rel_typein_hom rel top).toRelEmbedding.lift_wo

def typein (rel: α -> α -> Prop) [Relation.IsWellOrder rel] (top: α) := Ordinal.type (rel_typein rel top)
def typein' (rel: α -> α -> Prop) (h: Relation.IsWellOrder rel) (top: α) := typein rel top

def typein_surj (rel: α -> α -> Prop) [Relation.IsWellOrder rel] : ∀o < type rel, ∃top, o = typein rel top := by
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

def typein_lt_type (rel: α -> α -> Prop) [Relation.IsWellOrder rel] (top: α) : typein rel top < type rel := ⟨rel_typein_hom rel top⟩
def typein_lt_typein_iff (rel: α -> α -> Prop) [Relation.IsWellOrder rel] (a b: α) : typein rel a < typein rel b ↔ rel a b := by
  symm; apply Iff.intro
  · intro h
    exact ⟨{
      toFun x := {
        val := x.val
        property := trans x.property h
      }
      inj' := by
        intro ⟨x, xLt⟩ ⟨y, yLt⟩ h
        cases h; rfl
      resp_rel := Iff.rfl
      exists_top := by
        exists ⟨a, h⟩
        intro x
        dsimp; dsimp at x
        apply Iff.intro
        · intro g
          refine ⟨⟨x.val, g⟩, ?_⟩
          rfl
        · intro g
          obtain ⟨⟨_, hx⟩, rfl⟩ := g
          assumption
    }⟩
  · intro ⟨h⟩
    dsimp at h
    let relb := h.trans (rel_typein_hom rel b)
    have eq : rel_typein_hom rel a = relb := Subsingleton.allEq _ _
    have princ_top: (rel_typein_hom rel a).IsPrincipalTop a := rel_typein_princ_top rel a
    rw [eq] at princ_top
    have ⟨top, htop⟩ := h.exists_top
    have top' : relb.IsPrincipalTop top := by apply h.top_of_lt_of_lt_of_le (rel_typein_hom rel b: _ ≼i rel) top htop
    rw [PrincipalSegment.top_unique' _ _ _ princ_top top']
    exact top.property

end Ordinal
