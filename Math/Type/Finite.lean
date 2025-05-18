import Math.Order.Fin
import Math.Data.Fin.Basic
import Math.Data.Fintype.Cases
import Math.Data.ENat.Defs

open Classical

class inductive IsFinite (α: Sort*): Prop where
| intro (limit: Nat) : (α ≃ Fin limit) -> IsFinite α

def IsFinite.existsEquiv (α: Sort*) [h: IsFinite α] : ∃card, _root_.Nonempty (α ≃ Fin card) :=
  have ⟨limit, eqv⟩ := h
  ⟨limit, ⟨eqv⟩⟩

def IsFinite.ofEmbedding {limit: Nat} (emb: α ↪ Fin limit) : IsFinite α := by
  replace ⟨limit, ⟨emb⟩, spec⟩ := Relation.exists_min (· < ·: Relation Nat) (P := fun limit => Nonempty (α ↪ Fin limit)) ⟨_, ⟨emb⟩⟩
  suffices Function.Surjective emb by
    have ⟨eqv, h⟩ := Equiv.ofBij ⟨emb.inj, this⟩
    exists limit
  intro x
  apply Classical.byContradiction
  intro hx
  simp at hx
  match limit with
  | limit + 1 =>
  apply spec limit
  apply Nat.lt_succ_self
  let f := emb.trans ((Equiv.fin_erase x).toEmbedding)
  suffices ∀x, (f x).isSome by
    refine ⟨?_⟩
    exact {
      toFun x := (f x).get (this _)
      inj' := by
        intro x y h
        exact f.inj (Option.get_inj.mp h)
    }
  intro a
  simp [f]
  rcases Nat.lt_trichotomy (emb a) x with g | g | g
  rw[ Equiv.apply_fin_erase_of_lt]
  rfl
  assumption
  exfalso
  apply hx a
  rw [←Fin.val_inj, g]
  rw[ Equiv.apply_fin_erase_of_gt]
  rfl
  assumption

noncomputable
def IsFinite.card α [IsFinite α] : Nat :=
  Classical.choose (existsEquiv α)
noncomputable
def IsFinite.toEquiv α [IsFinite α] : α ≃ Fin (card α) :=
  Classical.choice (Classical.choose_spec (existsEquiv α))

noncomputable def ENat.card (α: Type*) : ENat :=
  open scoped ENat in
  if _:IsFinite α then IsFinite.card α else ∞

noncomputable def ENat.card_spec (α: Type*) [IsFinite α] : α ≃ Fin (card α).toNat := by
  rw [card]
  rw [dif_pos]
  apply IsFinite.toEquiv
  assumption

noncomputable def Nat.card (α: Type*) : Nat :=
  (ENat.card α).toNat

noncomputable def Nat.card_spec (α: Type*) [IsFinite α] : α ≃ Fin (card α) :=
  ENat.card_spec _

def IsFinite.card_of_equiv (h: Nonempty (α ≃ β)) [IsFinite α] [IsFinite β] : IsFinite.card α = IsFinite.card β := by
  obtain ⟨h⟩ := h
  have := ((toEquiv β).symm.trans <| h.symm.trans (toEquiv α)).symm
  exact Fin.eq_of_equiv this

noncomputable def IsFinite.equiv_of_card [IsFinite α] [IsFinite β] (h: IsFinite.card α = IsFinite.card β) : α ≃ β :=
  Classical.choice <| by
    have ha := IsFinite.toEquiv α
    have hb := IsFinite.toEquiv β
    rw [h] at ha
    exact ⟨ha.trans hb.symm⟩

noncomputable def ENat.equiv_of_card [IsFinite β] (h: card α = card β) : α ≃ β := by
    unfold card at h
    rename_i hb
    rw [dif_pos hb] at h
    have : IsFinite α := by
      split at h
      assumption
      contradiction
    rw [dif_pos] at h
    apply IsFinite.equiv_of_card
    rename_i g
    exact ENat.natCast_inj h
    assumption

noncomputable
def Fintype.ofIsFinite (α: Type _) [IsFinite α] : Fintype α :=
  Fintype.ofEquiv (IsFinite.toEquiv α)

def IsFinite.card_eq_card (α: Type _) [IsFinite α] :
  IsFinite.card α = @Fintype.card α (Fintype.ofIsFinite α) := by
  let inst := Fintype.ofIsFinite α
  rw [Fintype.ofIsFinite, Fintype.card_eq_of_equiv (IsFinite.toEquiv α),
    Fintype.card_fin]

instance [f: Fintype α] : IsFinite α := by
  induction Fintype.equivFin α with | mk h =>
  exists Fintype.card α

instance {α β: Type*} [IsFinite α] [IsFinite β] : IsFinite (α ⊕ β) := by
  have := Fintype.ofIsFinite α
  have := Fintype.ofIsFinite β
  exact inferInstance

def IsFinite.ofEquiv {α β: Sort*} [hb: IsFinite β] (h: α ≃ β) : IsFinite α := by
  obtain ⟨limit, hb⟩ := hb
  apply IsFinite.intro limit
  exact h.trans hb

def IsFinite.ofEquiv' {α: Sort*} (β: Sort*) [hb: IsFinite β] (h: α ≃ β) : IsFinite α := by
  obtain ⟨limit, hb⟩ := hb
  apply IsFinite.intro limit
  exact h.trans hb

def IsFinite.ofEmbed {α: Sort*} (β: Sort*) [hb: IsFinite β] (h: α ↪ β) : IsFinite α := by
  obtain ⟨limit, hb⟩ := hb
  apply IsFinite.ofEmbedding (limit := limit)
  exact Equiv.congrEmbed .rfl hb h

def Nat.not_is_finite : ¬IsFinite ℕ := by
  intro h
  exact (Fintype.ofIsFinite ℕ).nat_not_fintype

instance (α: Sort*) [IsFinite α] : IsFinite (PLift α) :=
  IsFinite.ofEquiv (Equiv.plift _)
instance (α: Type*) [IsFinite α] : IsFinite (ULift α) :=
  IsFinite.ofEquiv (Equiv.ulift _)

instance {α β: Sort*} [ha: IsFinite α] [hb: IsFinite β] : IsFinite (α ⊕' β) := by
  apply IsFinite.ofEquiv' (PLift α ⊕ PLift β)
  apply Equiv.trans
  apply Equiv.congrPSum
  apply (Equiv.plift _).symm
  apply (Equiv.plift _).symm
  apply (Equiv.sum_equiv_psum _ _).symm

instance {α: Sort*} {β: α -> Sort*} [IsFinite α]  [hb: ∀x, IsFinite (β x)] : IsFinite ((x: α) ×' β x) := by
  have := Fintype.ofIsFinite (PLift α)
  have : ∀x: PLift α, Fintype (PLift (β x.down)) := fun ⟨x⟩ =>
    Fintype.ofIsFinite (PLift (β x))
  apply IsFinite.ofEquiv' ((x : PLift α) × PLift (β x.down))
  apply Equiv.trans  _ (Equiv.sigma_equiv_psigma _).symm
  apply Equiv.congrPSigma (Equiv.plift _).symm
  intro x
  apply Equiv.trans _ (Equiv.plift _).symm
  rfl

instance {α: Type*} {β: α -> Type*} [IsFinite α]  [hb: ∀x, IsFinite (β x)] : IsFinite ((x: α) × β x) := by
  apply IsFinite.ofEquiv' ((x : α) ×' (β x))
  exact Equiv.sigma_equiv_psigma β

instance {α: Type*} {β: Type*} [IsFinite α]  [IsFinite β] : IsFinite (α × β) := by
  have := Fintype.ofIsFinite α
  have := Fintype.ofIsFinite β
  exact inferInstance

instance {α: Sort*} {β: Sort*} [IsFinite α]  [IsFinite β] : IsFinite (α ×' β) := by
  apply IsFinite.ofEquiv' (PLift α × PLift β)
  apply Equiv.trans
  apply Equiv.congrPProd
  apply (Equiv.plift _).symm
  apply (Equiv.plift _).symm
  apply (Equiv.prod_equiv_pprod _ _).symm

instance {α: Sort*} {β: α -> Sort*} [IsFinite α]  [∀x, IsFinite (β x)] : IsFinite (∀x, β x) := by
  have := Fintype.ofIsFinite (PLift α)
  have := fun x: PLift α => Fintype.ofIsFinite (PLift (β x.down))
  apply IsFinite.ofEquiv' (∀x: PLift α, PLift (β x.down))
  apply Equiv.mk
  case toFun =>
    intro f ⟨x⟩
    exact ⟨f x⟩
  case invFun =>
    intro f x
    exact (f ⟨x⟩).down
  case leftInv => intro _; rfl
  case rightInv => intro _; rfl

instance {α: Sort*} {β: Sort*} [IsFinite α] [IsFinite β] : IsFinite (α -> β) := inferInstance

instance {α: Sort*} {P: α -> Prop} [IsFinite α] : IsFinite (Subtype P) := by
  have := Fintype.ofIsFinite (PLift α)
  apply IsFinite.ofEquiv' (Subtype fun x: PLift α => P x.down)
  apply Equiv.congrSubtype _ _
  apply (Equiv.plift _).symm
  rfl

instance {α: Sort*} {P Q: α -> Prop} [hp: IsFinite (Subtype P)] [hq: IsFinite (Subtype Q)] : IsFinite (Subtype (fun x => P x ∨ Q x)) := by
  obtain ⟨cardp, peqv⟩ := hp
  obtain ⟨cardq, qeqv⟩ := hq
  apply IsFinite.ofEmbedding (limit := cardp + cardq)
  apply Embedding.mk
  case toFun =>
    intro ⟨x, h⟩
    if g:P x then
      exact (peqv ⟨x, g⟩).addNat cardq
    else
      exact (qeqv ⟨x, h.resolve_left g⟩).castLE (Nat.le_add_left _ _)
  case inj' =>
    intro ⟨x, hx⟩ ⟨y, hy⟩ eq
    dsimp at eq
    split at eq <;> split at eq <;> rename_i gx gy
    cases peqv.inj (Fin.addNat_inj eq)
    rfl
    replace eq := Fin.val_inj.mpr eq
    dsimp at eq
    have : qeqv ⟨y, Or.resolve_left hy gy⟩ < cardq := Fin.isLt _
    rw [←eq] at this
    have := Nat.not_le_of_lt this (Nat.le_add_left _ _)
    contradiction
    replace eq := Fin.val_inj.mpr eq
    dsimp at eq
    have : qeqv ⟨x, Or.resolve_left hx gx⟩ < cardq := Fin.isLt _
    rw [eq] at this
    have := Nat.not_le_of_lt this (Nat.le_add_left _ _)
    contradiction
    congr
    replace eq := Fin.val_inj.mpr eq
    dsimp at eq
    replace eq := Fin.val_inj.mp eq
    cases qeqv.inj eq
    rfl

instance {α: Sort*} {P Q: α -> Prop} [IsFinite (Subtype P)] : IsFinite (Subtype (fun x => P x ∧ Q x)) := by
  apply IsFinite.ofEmbed (Subtype P)
  refine ⟨?_, ?_⟩
  intro ⟨x, h, g⟩
  exact ⟨x, h⟩
  intro ⟨_, _, _⟩ ⟨_, _, _⟩ eq; cases eq; rfl

instance {α: Sort*} {P Q: α -> Prop} [IsFinite (Subtype Q)] : IsFinite (Subtype (fun x => P x ∧ Q x)) := by
  apply IsFinite.ofEmbed (Subtype Q)
  refine ⟨?_, ?_⟩
  intro ⟨x, h, g⟩
  exact ⟨x, g⟩
  intro ⟨_, _, _⟩ ⟨_, _, _⟩ eq; cases eq; rfl

instance [IsEmpty α] : IsFinite α := by
  apply IsFinite.intro 0
  apply Equiv.empty

instance [Subsingleton α] [h: Nonempty α] : IsFinite α := by
  obtain ⟨x⟩ := h
  apply IsFinite.intro 1
  apply Equiv.mk (fun _ => 0) (fun _ => x)
  intro x
  apply Subsingleton.allEq
  intro x
  apply Subsingleton.allEq

instance [hs: Subsingleton α] : IsFinite α := by
  by_cases h:Nonempty α
  · infer_instance
  · have := IsEmpty.ofNotNonempty h
    infer_instance

instance [IsFinite α] : IsFinite (Option α) := by
  have := Fintype.ofIsFinite α
  infer_instance

def Option.card'_eq [IsFinite α] :
  IsFinite.card (Option α) = IsFinite.card α + 1 := by
  have := Fintype.ofIsFinite α
  rw [IsFinite.card_eq_card, IsFinite.card_eq_card, Fintype.card_option]

instance {r: α -> α -> Prop} [IsFinite α] : IsFinite (Quot r) := by
  apply IsFinite.ofEmbed α
  refine {
    toFun x := Classical.choose x.exists_rep
    inj' := ?_
  }
  intro x y eq
  dsimp at eq
  rw [←Classical.choose_spec x.exists_rep, ←Classical.choose_spec y.exists_rep, eq]

instance {s: Setoid α} [IsFinite α] : IsFinite (Quotient s) :=
  inferInstanceAs (IsFinite (Quot _))

def IsFinite.subsingleton (h: ENat.card α ≤ 1) : Subsingleton α where
  allEq := by
    intro a b
    unfold ENat.card at h
    split at h
    · have := IsFinite.toEquiv α
      apply this.inj
      cases h
      rename_i h
      revert h this
      generalize IsFinite.card α = c
      intros
      match c with
      | 0 | 1 =>
      apply Subsingleton.allEq
    · contradiction

def IsFinite.subsingleton' [f: IsFinite α] (h: Nat.card α ≤ 1) : Subsingleton α where
  allEq := by
    intro a b
    have := Nat.card_spec α
    apply this.inj
    revert h this
    generalize Nat.card α = c
    intros
    match c with
    | 0 | 1 =>
    apply Subsingleton.allEq

open scoped ENat

noncomputable def IsFinite.existsEmbedding [IsFinite α] (h: ENat.card α ≤ ENat.card β) : α ↪ β :=
  Classical.choice <| by
    suffices IsFinite α -> ¬IsFinite β -> Nonempty (α ↪ β) by
      unfold ENat.card at h
      rw [dif_pos (inferInstanceAs (IsFinite α))] at h
      · split at h
        · simp at h
          have := IsFinite.toEquiv α
          have := IsFinite.toEquiv β
          refine ⟨?_⟩
          apply Equiv.congrEmbed _ _ (Fin.embedFin h)
          symm; assumption
          symm; assumption
        · clear h
          apply this
          assumption
          assumption
    intro fa fb
    clear h
    replace fa := (Fintype.ofIsFinite α)
    induction fa using Fintype.typeInduction with
    | eqv α₀ α₁ h _ ih =>
      have ⟨f⟩ := ih
      refine ⟨?_⟩
      apply Equiv.congrEmbed _ _ f
      assumption
      rfl
    | empty => exact ⟨Embedding.empty⟩
    | option α _ ih =>
      obtain ⟨ih⟩ := ih
      have : (Set.range ih)ᶜ.Nonempty := by
        rw [←Set.ne_empty, ←Set.compl_compl ∅]
        show ¬_
        rw [Set.compl_inj.eq_iff]
        intro h; simp [Set.range_eq_univ_iff_surjective] at h
        have ⟨h, _⟩  := Equiv.ofBij ⟨ih.inj, h⟩
        have := IsFinite.ofEquiv h.symm
        contradiction
      obtain ⟨x, hx⟩ := this
      refine ⟨?_⟩
      exact {
        toFun
        | .none => x
        | .some a => ih a
        inj' := by
          intro a b h
          cases a <;> cases b <;> simp at h
          rfl
          subst x; exfalso; apply hx
          apply Set.mem_range'
          subst x; exfalso; apply hx
          apply Set.mem_range'
          rw [ih.inj.eq_iff] at h
          rw [h]
      }

def ENat.card_of_embed_nat (h: ℕ ↪ α) : ENat.card α = ∞ := by
  rw [card, dif_neg]
  intro g
  have := IsFinite.ofEmbed _ h
  have := Nat.not_is_finite
  contradiction

def ENat.card_nat : ENat.card ℕ = ∞ := by
  apply card_of_embed_nat; rfl

def ENat.card_int : ENat.card ℤ = ∞ := by
  apply card_of_embed_nat
  exact {
    toFun := Int.ofNat
    inj' _ _ := Int.ofNat.inj
  }

def ENat.card_fin : ENat.card (Fin n) = n := by
  unfold card
  rw [dif_pos]
  congr
  symm
  apply Fin.eq_of_equiv
  apply IsFinite.toEquiv

def ENat.card_empty : IsEmpty α ↔ ENat.card α = 0 := by
  apply Iff.intro
  · intro
    rw [card, dif_pos]
    congr; apply Fin.eq_of_equiv
    symm; apply flip Equiv.trans
    apply IsFinite.toEquiv
    exact Equiv.empty
  · intro h
    rw [←ENat.natCast_zero, ←card_fin] at h
    have := ENat.equiv_of_card h
    exact { elim x := (this x).elim0 }
