import Math.Relation.Basic
import Math.Relation.RelIso
import Math.Tactics.PPWithUniv
import Math.Relation.Segments
import Math.Order.Linear

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

private
def ulift_rel (r: α -> α -> Prop) (a b: ULift α) : Prop := r a.down b.down

private
def ulift_rel_equiv (r: α -> α -> Prop) : r ≃r ulift_rel r where
  toEquiv := ULift.equiv.symm
  resp_rel := Iff.rfl

private
instance (r: α -> α -> Prop) [Relation.IsWellOrder r] : Relation.IsWellOrder (ulift_rel r) where
  toIsWellFounded := (ulift_rel_equiv _).symm.wf
  toIsTrichotomous := (ulift_rel_equiv _).tri
  toIsTrans := (ulift_rel_equiv _).trans'

def Pre.lift (a: Pre.{u}): Pre.{max u v} where
  ty := ULift a.ty
  rel := ulift_rel a.rel

def lift : Ordinal -> Ordinal := by
  apply Quotient.lift (fun _ => ⟦_⟧) _
  exact Pre.lift
  intro a b ⟨eq⟩
  apply sound
  apply RelIso.trans (ulift_rel_equiv _).symm
  apply RelIso.trans _ (ulift_rel_equiv _)
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

def Pre.ofNat (n: Nat) : Pre where
  ty := Fin n
  rel a b := a < b
  wo := {
    tri a b := by
      rw [←Fin.val_inj]
      exact Nat.lt_trichotomy a b
    trans := Nat.lt_trans
    wf := by
      apply WellFounded.intro
      intro ⟨a, aLt⟩
      induction a using Nat.lt_wfRel.wf.induction with
      | h a ih =>
      apply Acc.intro
      intro b lt
      apply ih
      assumption
  }

def Ordinal.ofNat (n: Nat) := ⟦Pre.ofNat n⟧

instance : OfNat Pre n := ⟨(Pre.ofNat n).lift⟩
instance : OfNat Ordinal n := ⟨(Ordinal.ofNat n).lift⟩

end Ordinal
