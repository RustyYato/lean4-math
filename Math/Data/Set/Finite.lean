import Math.Data.Set.Basic
import Math.Order.Fin
import Math.Type.Finite

namespace Set

-- a set is finite if there exists an embedding from elements of the set to Fin n for some n
abbrev IsFinite (a: Set α): Prop := _root_.IsFinite a.Elem

-- a set is co-finite if the complement is finite
abbrev IsCoFinite (a: Set α): Prop := IsFinite aᶜ

def IsFinite.existsEquiv {a: Set α} (h: a.IsFinite) : ∃card, _root_.Nonempty (a.Elem ≃ Fin card) :=
  _root_.IsFinite.existsEquiv a.Elem

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

def Set.elem_val_eq_of_elem_heq (a b: Set α) (c: a.Elem) (d: b.Elem) : a = b -> HEq c d -> c.val = d.val := by
  intro eq heq
  cases eq
  cases heq
  rfl

def Set.IsFinite.sUnion (a: Set (Set α)) [ha: IsFinite a] (hx: ∀x ∈ a, IsFinite x) : IsFinite (⋃ a) := by
  have ⟨lim, emb⟩  := _root_.IsFinite.ofPSigma (α := a.Elem) (β := fun x: a.Elem => x.val.Elem) (ha := ha) (hb := fun x => hx x.val x.property)
  apply IsFinite.intro lim
  apply Embedding.comp
  assumption
  apply Embedding.mk
  case toFun =>
    intro x
    have := mem_sUnion.mp x.property
    let a' := Classical.choose this
    have : a' ∈ a ∧ x.val ∈ a' := Classical.choose_spec this
    refine PSigma.mk ⟨a', ?_⟩ ⟨x.val, ?_⟩
    exact this.left
    exact this.right
  case inj =>
    dsimp
    intro x y eq
    dsimp at eq
    injection eq with aeq beq
    injection aeq with eq
    let x' := Classical.choose x.property
    let y' := Classical.choose y.property
    obtain eq : x' = y' := eq
    have x₀: x' ∈ a ∧ x.val ∈ x' := Classical.choose_spec x.property
    have y₀: y' ∈ a ∧ y.val ∈ y' := Classical.choose_spec y.property
    obtain ⟨a₀, ha₀⟩ := x₀
    obtain ⟨b₀, hb₀⟩ := y₀
    have := Set.elem_val_eq_of_elem_heq x' y' ⟨_, ha₀⟩ ⟨_, hb₀⟩ eq beq
    simp at this
    cases x with | mk x xprop =>
    cases y with | mk y yprop =>
    dsimp at beq
    congr

def Set.IsFinite.sInter (a: Set (Set α)) (hx: ∃x ∈ a, IsFinite x) : IsFinite (⋂ a) := by
  obtain ⟨a', a'_in_a, lim, emb⟩ := hx
  apply IsFinite.intro lim
  apply Embedding.comp emb
  clear emb
  apply Embedding.mk
  case toFun =>
    intro x
    apply Subtype.mk x.val
    apply x.property
    assumption
  case inj =>
    intro ⟨x, _⟩ ⟨y, _⟩ h
    simp at h
    cases h
    rfl

instance : IsFinite (∅: Set α) := by
  apply IsFinite.intro 0
  apply Embedding.mk
  intro x y eq
  have := x.property
  contradiction
  intro x
  have := x.property
  contradiction

instance : IsFinite ({a}: Set α) := by
  apply IsFinite.intro 1
  apply Embedding.mk
  case toFun =>
    intro
    exact 0
  intro ⟨x, xprop⟩ ⟨y, yprop⟩ eq
  cases yprop
  cases xprop
  rfl

instance {a: α} {as: Set α} [IsFinite as] : IsFinite (Insert.insert a as) :=
  inferInstanceAs (IsFinite ({ a } ∪ as))

instance {as: Set α} {f: α -> β} [ha: IsFinite as] : IsFinite (Set.image as f) := by
  obtain ⟨lim, emb⟩ := ha
  apply IsFinite.intro lim
  apply Embedding.comp emb
  clear emb
  apply Embedding.mk
  case toFun =>
    intro ⟨x, xprop⟩
    apply Subtype.mk (Classical.choose xprop)
    exact (Classical.choose_spec xprop).left
  case inj =>
    intro ⟨x, xprop⟩ ⟨y, yprop⟩ eq
    simp at eq
    replace eq := Subtype.mk.inj eq
    have ⟨_, h₀⟩ := Classical.choose_spec xprop
    have ⟨_, h₁⟩ := Classical.choose_spec yprop
    rw [←eq] at h₁
    congr
    rw [h₀, h₁]

open Classical in
instance {as: Set α} [ha: IsFinite as] : IsFinite as.powerset := by
  let card := _root_.IsFinite.card as.Elem
  have eqv: as.Elem ≃ Fin card := _root_.IsFinite.toEquiv as.Elem
  apply IsFinite.intro (2 ^ card)
  apply Embedding.mk
  case toFun =>
    intro x
    apply Fin.mk <| Fin.powTwoSum fun y: Fin card => (eqv.invFun y).val ∈ x.val
    apply Fin.powTwoSum_lt
  case inj =>
    intro x y eq
    simp at eq
    have := congrFun (Fin.powTwoSum_inj eq)
    simp at this
    cases x with | mk x xprop =>
    cases y with | mk y yprop =>
    congr
    ext z
    apply Iff.intro
    intro mem_x
    have := (this (eqv.toFun ⟨_, xprop _ mem_x⟩)).mp
    rw [eqv.leftInv] at this
    apply this
    assumption
    intro mem_y
    have := (this (eqv.toFun ⟨_, yprop _ mem_y⟩)).mpr
    rw [eqv.leftInv] at this
    apply this
    assumption

end Set
