import Math.Data.Set.Basic
import Math.Order.Fin
import Math.Type.Finite

namespace Set

open Classical

-- a set is finite if there exists an embedding from elements of the set to Fin n for some n
protected abbrev IsFinite (a: Set α): Prop := _root_.IsFinite a.Elem

-- a set is co-finite if the complement is finite
protected abbrev IsCoFinite (a: Set α): Prop := Set.IsFinite aᶜ

instance [ha: _root_.IsFinite α] : _root_.IsFinite (Set α) := by
  apply IsFinite.ofEmbed (α -> Bool)
  refine ⟨?_, ?_⟩
  intro s a
  exact decide (a ∈ s)
  intro x y eq
  dsimp at eq
  replace eq := congrFun eq
  conv at eq => { intro; rw [decide_eq_decide] }
  ext a
  rw [eq]

def IsFinite.existsEquiv {a: Set α} (h: a.IsFinite) : ∃card, _root_.Nonempty (a.Elem ≃ Fin card) :=
  _root_.IsFinite.existsEquiv a.Elem

instance Set.IsFinite.ofFin (x: Set (Fin n)) : x.IsFinite := by
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

instance [ha: Set.IsFinite a] [hb: Set.IsFinite b] : Set.IsFinite (a ∪ b) := by
  have := Fintype.ofIsFinite a
  have := Fintype.ofIsFinite b
  unfold Set.Elem at *
  have : Fintype ((a ∪ b).Elem) := inferInstanceAs (Fintype (Subtype fun x => x ∈ a ∨ x ∈ b))
  infer_instance

instance [ha: Set.IsFinite a] : Set.IsFinite (a ∩ b) := by
  have := Fintype.ofIsFinite a
  unfold Set.Elem at *
  have : Fintype ((a ∩ b).Elem) := inferInstanceAs (Fintype (Subtype fun x => x ∈ a ∧ x ∈ b))
  infer_instance

instance [hb: Set.IsFinite b] : Set.IsFinite (a ∩ b) := by
  rw [Set.inter_comm]
  exact inferInstance

def Set.elem_val_eq_of_elem_heq (a b: Set α) (c: a.Elem) (d: b.Elem) : a = b -> HEq c d -> c.val = d.val := by
  intro eq heq
  cases eq
  cases heq
  rfl

def IsFinite.sUnion (a: Set (Set α)) [ha: Set.IsFinite a] (hx: ∀x: a, Set.IsFinite x.val) : Set.IsFinite (⋃ a) := by
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

def IsFinite.sInter (a: Set (Set α)) (hx: ∃x ∈ a, Set.IsFinite x) : Set.IsFinite (⋂ a) := by
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

instance : Set.IsFinite (∅: Set α) := by
  apply IsFinite.intro 0
  apply Equiv.mk
  case toFun => intro x; exact x.property.elim
  case invFun => intro x; exact x.elim0
  case leftInv => intro x; exact x.property.elim
  case rightInv => intro x; exact x.elim0

instance : Set.IsFinite ({a}: Set α) := by
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

instance {a: α} {as: Set α} [IsFinite as] : Set.IsFinite (Insert.insert a as) :=
  inferInstanceAs (Set.IsFinite ({ a } ∪ as))

instance {as: Set α} {f: α -> β} [ha: Set.IsFinite as] : Set.IsFinite (Set.image as f) := by
  apply IsFinite.ofEmbed as
  apply Embedding.mk
  case toFun =>
    intro ⟨x, xprop⟩
    apply Subtype.mk (Classical.choose xprop)
    exact (Classical.choose_spec xprop).left
  case inj =>
    intro ⟨x, xprop⟩ ⟨y, yprop⟩ eq
    simp at eq
    have ⟨_, h₀⟩ := Classical.choose_spec xprop
    have ⟨_, h₁⟩ := Classical.choose_spec yprop
    rw [←eq] at h₁
    congr
    rw [h₀, h₁]

instance {as: Set α} [ha: Set.IsFinite as] : Set.IsFinite as.powerset := by
  apply IsFinite.ofEmbed (Set as)
  refine ⟨?_, ?_⟩
  intro ⟨x, hx⟩
  exact x.preimage Subtype.val
  apply Function.Injective.comp
  apply Set.mk.inj
  intro x y eq
  replace eq := congrFun eq
  dsimp at eq
  ext a
  apply Iff.intro
  intro h; apply (eq ⟨a, _⟩).mp
  assumption
  apply x.property; assumption
  intro h; apply (eq ⟨a, _⟩).mpr
  assumption
  apply y.property; assumption

def IsFinite.ofSubset (s t: Set α) [h: t.IsFinite] (h: s ⊆ t) : s.IsFinite := by
  apply IsFinite.ofEmbed (β := t)
  apply Embedding.mk
  case toFun =>
    intro x
    exact ⟨x.val, h _ x.property⟩
  case inj =>
    intro ⟨x, _⟩ ⟨y, _⟩ eq
    cases eq
    congr

def IsFinite.induction {motive : Set α → Prop} (s : Set α) [h : s.IsFinite]
    (nil: motive ∅)
    (cons : ∀ a s, a ∉ s → Set.IsFinite s → motive s → motive (insert a s)) : motive s := by
    obtain ⟨limit, eqv⟩ := h
    induction limit generalizing s with
    | zero =>
      suffices s = ∅ by
        subst s
        assumption
      apply ext_empty
      intro x mem
      exact (eqv ⟨x, mem⟩).elim0
    | succ h ih =>
      let x := eqv.invFun 0
      have : s = insert x.val (s \ {x.val}) := by
        ext y
        rw [mem_insert, mem_sdiff, mem_singleton]
        apply Iff.intro
        intro mem
        by_cases g:x.val = y
        rw [←g]
        left; rfl
        right
        apply And.intro
        assumption
        exact Ne.symm g
        intro h
        cases h
        subst y
        exact x.property
        rename_i g
        cases g
        assumption
      rw [this]
      clear this
      suffices (s \ {x.val}: Set _) ≃ Fin h by
        apply cons
        intro mem
        exact (Set.mem_sdiff.mp mem).right (Set.mem_singleton.mpr rfl)
        exists h
        apply ih
        assumption
      apply Equiv.mk
      case toFun =>
        intro ⟨y, hy⟩
        rw [mem_sdiff] at hy
        apply (eqv.toFun ⟨y, hy.left⟩).pred
        intro h
        have : ⟨y, hy.left⟩ = x := by
          show _ = eqv.invFun 0
          rw [←h, eqv.leftInv]
        apply hy.right
        rw [mem_singleton]
        rw [←this]
      case invFun =>
        intro y
        let y' := eqv.invFun y.succ
        refine ⟨y'.val, ?_⟩
        rw [mem_sdiff, mem_singleton]
        apply And.intro
        exact y'.property
        intro g
        replace g := Subtype.ext g
        have := Fin.val_inj.mpr (eqv.invFun_inj g)
        contradiction
      case leftInv =>
        intro ⟨y, hy⟩
        dsimp; rw [mem_sdiff, mem_singleton] at hy
        congr
        rw [Fin.succ_pred, eqv.leftInv]
      case rightInv =>
        intro y
        dsimp
        rw [Fin.pred_eq_iff_eq_succ]
        show eqv.toFun (eqv.invFun _) = _
        rw [eqv.rightInv]

def IsFinite.spec (s: Set α) [h: s.IsFinite] : ∃s': List α, s'.Nodup ∧ ∀x, x ∈ s ↔ x ∈ s' := by
  induction s using Set.IsFinite.induction with
  | nil =>
    exists []
    apply And.intro
    apply List.Pairwise.nil
    intro x
    apply Iff.intro
    intro; contradiction
    intro; contradiction
  | cons x s x_notin_s s_fin ih =>
    obtain ⟨as, nodup, eqv⟩ := ih
    exists x::as
    apply And.intro
    apply List.Pairwise.cons
    intro y ymemas
    have := (eqv _).mpr ymemas
    intro g; subst g
    contradiction
    assumption
    intro y
    rw [mem_insert, List.mem_cons, eqv]

instance (n: Nat) : Set.IsFinite (Set.mk (· < n)) := by
  apply IsFinite.intro n
  exact (Fin.equivSubtype n).symm

instance (n: Nat) : Set.IsFinite (Set.mk (· ≤ n)) := by
  suffices Set.mk (· ≤ n) = Set.mk (· < (n + 1)) by
    rw [this]
    infer_instance
  ext x
  apply Nat.le_iff_lt_add_one

instance [IsFinite α] (s: Set α) : Set.IsFinite s := by
  apply IsFinite.ofEmbed α
  exact Subtype.embed

end Set
