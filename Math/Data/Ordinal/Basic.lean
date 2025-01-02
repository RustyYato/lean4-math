import Math.Relation.Basic
import Math.Relation.RelIso
import Math.Tactics.PPWithUniv

namespace Ordinal

@[pp_with_univ]
structure Pre.{u} where
  ty: Type u
  rel: ty -> ty -> Prop
  wf: Relation.IsWellOrder rel := by infer_instance

instance pre_setoid : Setoid Pre where
  r a b := Nonempty (a.rel ≃r b.rel)
  iseqv := {
    refl _ := ⟨RelIso.refl⟩
    symm | ⟨h⟩ => ⟨h.symm⟩
    trans | ⟨h⟩, ⟨g⟩ => ⟨h.trans g⟩
  }

@[pp_with_univ]
def Ordinal := Quotient pre_setoid
def Ordinal.mk : Pre -> Ordinal := Quotient.mk _
local notation "⟦" x "⟧" => Ordinal.mk x
def Ordinal.ind : {motive: Ordinal -> Prop} -> (mk: ∀a, motive ⟦a⟧) -> ∀a, motive a := Quotient.ind
def Ordinal.ind₂ : {motive: Ordinal -> Ordinal -> Prop} -> (mk: ∀a b, motive ⟦a⟧ ⟦b⟧) -> ∀a b, motive a b := Quotient.ind₂
def Ordinal.ind₃ : {motive: Ordinal -> Ordinal -> Ordinal -> Prop} -> (mk: ∀a b c, motive ⟦a⟧ ⟦b⟧ ⟦c⟧) -> ∀a b c, motive a b c := by
  intro motive h a b c
  induction a, b using ind₂ with | mk a b =>
  induction c using ind with | mk c =>
  apply h
def Ordinal.ind₄ : {motive: Ordinal -> Ordinal -> Ordinal -> Ordinal -> Prop} -> (mk: ∀a b c d, motive ⟦a⟧ ⟦b⟧ ⟦c⟧ ⟦d⟧) -> ∀a b c d, motive a b c d := by
  intro motive h a b c d
  induction a, b using ind₂ with | mk a b =>
  induction c, d using ind₂ with | mk c d =>
  apply h

def Ordinal.type (rel: α -> α -> Prop) [Relation.IsWellOrder rel] := ⟦.mk _ rel⟧

end Ordinal
