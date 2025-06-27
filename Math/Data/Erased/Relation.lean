import Math.Data.Erased.Basic
import Math.Relation.Defs
import Math.Relation.RelIso

namespace Erased

def relEmbed (r: α -> α -> Prop) : r ↪r Erased.liftRel r where
  toEmbedding := mk
  resp_rel := by
    intro a b
    apply Iff.intro
    · intro
      exists a
      exists b
    · intro ⟨_, _, _, rfl, rfl⟩
      assumption

instance {r: α -> α -> Prop} [Relation.IsWellFounded r] : Relation.IsWellFounded (Erased.liftRel r) where
  wf := by
    apply WellFounded.intro
    intro a; induction a with | mk a =>
    induction a using Relation.wfInduction r with
    | h a ih =>
    apply Acc.intro
    intro b
    induction b with | mk b =>
    rintro ⟨a, b, h, rfl, rfl⟩
    apply ih
    assumption

instance {r: α -> α -> Prop} [Relation.IsTrans r] : Relation.IsTrans (Erased.liftRel r) where
  trans := by
    rintro a b c
    induction a with | mk a =>
    induction b with | mk b =>
    induction c with | mk c =>
    rintro ⟨a, b, h, rfl, rfl⟩ ⟨b, c, g, rfl, rfl⟩
    refine ⟨_, _, ?_, rfl, rfl⟩
    apply Relation.trans'
    assumption
    assumption

instance {r: α -> α -> Prop} [Relation.IsSymmetric r] : Relation.IsSymmetric (Erased.liftRel r) where
  symm := by
    rintro a b
    induction a with | mk a =>
    induction b with | mk b =>
    rintro ⟨a, b, h, rfl, rfl⟩
    exists b
    exists a
    apply And.intro
    apply Relation.symm
    assumption
    trivial

instance {r: α -> α -> Prop} [Relation.IsRefl r] : Relation.IsRefl (Erased.liftRel r) where
  refl := by
    rintro a
    induction a with | mk a =>
    refine ⟨a, a, ?_, rfl, rfl⟩
    rfl

instance {r: α -> α -> Prop} [Relation.IsAsymm r] : Relation.IsAsymm (Erased.liftRel r) where
  asymm := by
    rintro a b
    induction a with | mk a =>
    induction b with | mk b =>
    rintro ⟨a, b, h, rfl, rfl⟩ ⟨b, c, g, rfl, rfl⟩
    exact Relation.asymm h g

instance {r: α -> α -> Prop} [Relation.IsIrrefl r] : Relation.IsIrrefl (Erased.liftRel r) where
  irrefl := by
    rintro a
    induction a with | mk a =>
    rintro ⟨a, b, h, rfl, rfl⟩
    exact Relation.irrefl h

instance {r: α -> α -> Prop} [Relation.IsAntisymm r] : Relation.IsAntisymm (Erased.liftRel r) where
  antisymm_by := by
    rintro a b
    induction a with | mk a =>
    induction b with | mk b =>
    rintro ⟨a, b, h, rfl, rfl⟩ ⟨a, b, g, rfl, rfl⟩
    congr
    apply antisymm _ h
    assumption

instance {r: α -> α -> Prop} [Relation.IsConnected r] : Relation.IsConnected (Erased.liftRel r) where
  connected_by := by
    rintro a b
    induction a with | mk a =>
    induction b with | mk b =>
    rcases Relation.connected r a b with h | rfl | h
    · left
      exists a
      exists b
    · right; left
      rfl
    · right; right
      exists b
      exists a

-- Erased.liftRel preserves all orders

instance {r: α -> α -> Prop} [Relation.IsPreorder r] : Relation.IsPreorder (Erased.liftRel r) where
instance {r: α -> α -> Prop} [Relation.IsPartialOrder r (· = ·)] : Relation.IsPartialOrder (Erased.liftRel r) (· = ·) where
instance {r: α -> α -> Prop} [Relation.IsLinearOrder r (· = ·)] : Relation.IsLinearOrder (Erased.liftRel r) (· = ·) where
instance {r: α -> α -> Prop} [Relation.IsStrictPartialOrder r] : Relation.IsStrictPartialOrder (Erased.liftRel r) where
instance {r: α -> α -> Prop} [Relation.IsStrictLinearOrder r (· = ·)] : Relation.IsStrictLinearOrder (Erased.liftRel r) (· = ·) where
instance {r: α -> α -> Prop} [Relation.IsWellOrder r] : Relation.IsWellOrder (Erased.liftRel r) where

instance [wf: WellFoundedRelation α] : WellFoundedRelation (Erased α) where
  rel := Erased.liftRel wf.rel
  wf :=
    have : Relation.IsWellFounded wf.rel := ⟨wf.wf⟩
    Relation.wellFounded (Erased.liftRel wf.rel)

end Erased
