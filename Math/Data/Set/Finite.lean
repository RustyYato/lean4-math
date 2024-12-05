import Math.Data.Set.Basic
import Math.Order.Fin
import Math.Type.Finite

namespace Set

-- a set is finite if there exists an embedding from elements of the set to Fin n for some n
abbrev IsFinite (a: Set α): Prop := _root_.IsFinite a.Elem

-- a set is co-finite if the complement is finite
abbrev IsCoFinite (a: Set α): Prop := IsFinite aᶜ

def IsFinite.existsIso {a: Set α} (h: a.IsFinite) : ∃card, _root_.Nonempty (a.Elem ≃ Fin card) :=
  Type.IsFinite.existsIso a.Elem

instance IsFinite.ofFin (x: Set (Fin n)) : x.IsFinite := by
  apply IsFinite.intro n
  apply Embedding.mk Subtype.val
  intro ⟨x,_⟩ ⟨y, _⟩  eq
  cases eq
  rfl

def Fin.castLE_ne_addNat (x: Fin n) (y: Fin m) : x.castLE (Nat.le_add_left _ _) ≠ y.addNat n := by
  intro h
  cases x with | mk x xLt =>
  cases y with | mk y yLt =>
  unfold Fin.castLE Fin.addNat at h
  dsimp at h
  have := Fin.mk.inj h
  subst x
  exact Nat.not_lt_of_le (Nat.le_add_left _ _) xLt

instance [ha: IsFinite a] [hb: IsFinite b] : IsFinite (a ∪ b) := by
  obtain ⟨alim, aemb⟩ := ha
  obtain ⟨blim, bemb⟩ := hb
  apply IsFinite.intro (alim + blim)
  apply Embedding.mk
  case toFun =>
    intro x
    match Classical.propDecidable (x.val ∈ b) with
    | .isTrue h =>
      apply (bemb ⟨x.val, h⟩).castLE
      apply Nat.le_add_left
    | .isFalse h =>
      apply Fin.addNat
      apply aemb.toFun
      exists x.val
      cases x.property
      assumption
      contradiction
  case inj =>
    intro x y eq
    dsimp at eq
    split at eq <;> split at eq
    · have := bemb.inj (Fin.val_inj.mp (Fin.mk.inj eq))
      cases x; cases y
      congr
      cases this
      rfl
    · have := Fin.castLE_ne_addNat _ _ eq
      contradiction
    · have := Fin.castLE_ne_addNat _ _ eq.symm
      contradiction
    · have := aemb.inj <| Fin.val_inj.mp (Nat.add_right_cancel_iff.mp (Fin.mk.inj eq))
      cases x; cases y; cases this
      rfl

instance [ha: IsFinite a] : IsFinite (a ∩ b) := by
  obtain ⟨lim, emb⟩ := ha
  apply IsFinite.intro lim
  apply Embedding.mk
  case toFun =>
    intro x
    apply emb.toFun
    apply Subtype.mk x.val
    exact x.property.left
  case inj =>
    intro x y eq
    dsimp at eq
    cases x; cases y; cases (emb.inj eq)
    rfl

instance [hb: IsFinite b] : IsFinite (a ∩ b) := by
  obtain ⟨lim, emb⟩ := hb
  apply IsFinite.intro lim
  apply Embedding.mk
  case toFun =>
    intro x
    apply emb.toFun
    apply Subtype.mk x.val
    exact x.property.right
  case inj =>
    intro x y eq
    dsimp at eq
    cases x; cases y; cases (emb.inj eq)
    rfl

instance {a: Set (Set α)} [∀x: a.Elem, IsFinite x] : IsFinite (⋂a) where
instance {a: Set (Set α)} [∃x ∈ a, IsFinite x] : IsFinite (⋂a) where

end Set
