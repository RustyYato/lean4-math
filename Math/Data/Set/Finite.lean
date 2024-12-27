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
  unfold Set.IsFinite Set.Elem
  exact inferInstance

def Fin.castLE_ne_addNat (x: Fin n) (y: Fin m) : x.castLE (Nat.le_add_left _ _) ≠ y.addNat n := by
  intro h
  cases x with | mk x xLt =>
  cases y with | mk y yLt =>
  unfold Fin.castLE Fin.addNat at h
  dsimp at h
  have := Fin.mk.inj h
  subst x
  exact Nat.not_lt_of_le (Nat.le_add_left _ _) xLt

open Classical in
instance [ha: IsFinite a] [hb: IsFinite b] : IsFinite (a ∪ b) := by
  have := Fintype.ofIsFinite a
  have := Fintype.ofIsFinite b
  unfold Set.Elem at *
  have : Fintype ((a ∪ b).Elem) := inferInstanceAs (Fintype (Subtype fun x => x ∈ a ∨ x ∈ b))
  infer_instance

open Classical in
instance [ha: IsFinite a] : IsFinite (a ∩ b) := by
  have := Fintype.ofIsFinite a
  unfold Set.Elem at *
  have : Fintype ((a ∩ b).Elem) := inferInstanceAs (Fintype (Subtype fun x => x ∈ a ∧ x ∈ b))
  infer_instance

instance [hb: IsFinite b] : IsFinite (a ∩ b) := by
  rw [Set.inter_comm]
  exact inferInstance

def Set.elem_val_eq_of_elem_heq (a b: Set α) (c: a.Elem) (d: b.Elem) : a = b -> HEq c d -> c.val = d.val := by
  intro eq heq
  cases eq
  cases heq
  rfl

def Set.IsFinite.sUnion (a: Set (Set α)) [ha: IsFinite a] (hx: ∀x: a, IsFinite x.val) : IsFinite (⋃ a) := by
  apply _root_.IsFinite.ofEmbed (Σa': a, a'.val)
  apply Embedding.mk
  case toFun =>
    intro ⟨x, hx⟩
    replace hx := mem_sUnion.mp hx
    let a' := Classical.choose hx
    have : a' ∈ a ∧ x ∈ a' := Classical.choose_spec hx
    refine Sigma.mk ⟨a', ?_⟩ ⟨x, ?_⟩
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
  obtain ⟨a', a'_in_a, lim, eqv⟩ := hx
  apply IsFinite.ofEmbedding (limit := lim)
  apply Embedding.congr _ (by rfl) eqv
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
  apply Equiv.mk
  case toFun => intro x; exact x.property.elim
  case invFun => intro x; exact x.elim0
  case leftInv => intro x; exact x.property.elim
  case rightInv => intro x; exact x.elim0

instance : IsFinite ({a}: Set α) := by
  apply IsFinite.intro 1
  apply Equiv.mk
  case toFun =>
    intro
    exact 0
  case invFun =>
    intro
    exact ⟨a, Set.mem_singleton.mpr rfl⟩
  case leftInv =>
    intro _
    apply Subsingleton.allEq
  case rightInv =>
    intro _
    apply Subsingleton.allEq

instance {a: α} {as: Set α} [IsFinite as] : IsFinite (Insert.insert a as) :=
  inferInstanceAs (IsFinite ({ a } ∪ as))

instance {as: Set α} {f: α -> β} [ha: IsFinite as] : IsFinite (Set.image as f) := by
  apply IsFinite.ofEmbed as
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
  apply IsFinite.ofEmbedding (limit := 2 ^ card)
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
