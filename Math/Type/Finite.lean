import Math.Type.Basic
import Math.Order.Fin
import Math.Data.Fin.Basic
import Math.Data.Fintype.Basic

class inductive IsFinite (α: Sort*): Prop where
| intro (limit: Nat) : (α ≃ Fin limit) -> IsFinite α

def IsFinite.existsEquiv (α: Sort*) [h: IsFinite α] : ∃card, _root_.Nonempty (α ≃ Fin card) :=
  have ⟨limit, eqv⟩ := h
  ⟨limit, ⟨eqv⟩⟩

def IsFinite.ofEmbedding {limit: Nat} (emb: α ↪ Fin limit) : IsFinite α := by
  induction limit with
  | zero =>
    exists 0
    apply Equiv.mk emb Fin.elim0
    intro x
    exact (emb x).elim0
    intro x
    exact x.elim0
  | succ limit ih =>
    if h:Function.Surjective emb then
      have ⟨_, _⟩ := Equiv.ofBij ⟨emb.inj, h⟩
      exists limit.succ
    else
      replace ⟨missing, not_in_range⟩ := Classical.not_forall.mp h
      replace not_in_range := not_exists.mp not_in_range
      apply ih
      apply Embedding.mk
      case toFun =>
        intro elem
        let out := emb elem
        if g:out ≤ missing then
          have : out < missing := lt_of_le_of_ne g (Ne.symm (not_in_range _))
          apply Fin.mk out.val
          apply lt_of_lt_of_le
          exact this
          apply Nat.le_of_lt_succ
          exact missing.isLt
        else
          replace g := lt_of_not_le g
          apply out.pred
          intro h
          rw [h] at g
          contradiction
      case inj =>
        intro x y eq
        dsimp at eq
        split at eq <;> split at eq
        exact emb.inj (Fin.val_inj.mp (Fin.mk.inj eq))
        · rename_i h g
          unfold Fin.pred Fin.subNat at eq
          replace eq := Fin.mk.inj eq
          have : emb x < missing := (lt_of_le_of_ne h (Ne.symm (not_in_range _)))
          replace := Fin.lt_def.mp this
          rw [eq] at this
          replace this := Nat.succ_lt_succ this
          rw [←Nat.add_one, Nat.sub_add_cancel] at this
          have := lt_of_lt_of_le this (Nat.succ_le_of_lt (lt_of_not_le g))
          have := lt_irrefl this
          contradiction
          apply Nat.succ_le_of_lt
          apply Nat.zero_lt_of_lt
          apply lt_of_not_le
          assumption
        · rename_i g h
          unfold Fin.pred Fin.subNat at eq
          replace eq := Fin.mk.inj eq
          have : emb y < missing := (lt_of_le_of_ne h (Ne.symm (not_in_range _)))
          replace := Fin.lt_def.mp this
          rw [←eq] at this
          replace this := Nat.succ_lt_succ this
          rw [←Nat.add_one, Nat.sub_add_cancel] at this
          have := lt_of_lt_of_le this (Nat.succ_le_of_lt (lt_of_not_le g))
          have := lt_irrefl this
          contradiction
          apply Nat.succ_le_of_lt
          apply Nat.zero_lt_of_lt
          apply lt_of_not_le
          assumption
        · exact emb.inj (Fin.pred_inj.mp eq)

noncomputable
def IsFinite.card α [IsFinite α] : Nat :=
  Classical.choose (existsEquiv α)
noncomputable
def IsFinite.toEquiv α [IsFinite α] : α ≃ Fin (card α) :=
  Classical.choice (Classical.choose_spec (existsEquiv α))

def IsFinite.card_of_equiv (h: Nonempty (α ≃ β)) [IsFinite α] [IsFinite β] : IsFinite.card α = IsFinite.card β := by
  obtain ⟨h⟩ := h
  have := ((toEquiv β).symm.trans <| h.symm.trans (toEquiv α)).symm
  exact Fin.eqOfEquiv this

noncomputable
def Fintype.ofIsFinite (α: Type _) [IsFinite α] : Fintype α :=
  Fintype.ofEquiv (IsFinite.toEquiv α)

def IsFinite.card_eq_card (α: Type _) [IsFinite α] :
  IsFinite.card α = @Fintype.card α (Fintype.ofIsFinite α) := by
  rw [Fintype.ofIsFinite, Fintype.eqCardOfEquiv (IsFinite.toEquiv α),
    Fin.card_eq]
  infer_instance

open Classical in
instance [f: Fintype α] : IsFinite α := by
  exists Fintype.card α
  apply Fintype.equivFin

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
  apply Embedding.congr
  assumption
  rfl
  assumption

instance (α: Sort*) [IsFinite α] : IsFinite (PLift α) :=
  IsFinite.ofEquiv PLift.equiv
instance (α: Type*) [IsFinite α] : IsFinite (ULift α) :=
  IsFinite.ofEquiv ULift.equiv

instance {α β: Sort*} [ha: IsFinite α] [hb: IsFinite β] : IsFinite (α ⊕' β) := by
  apply IsFinite.ofEquiv' (PLift α ⊕ PLift β)
  apply Equiv.trans
  apply PSum.equivCongr
  apply PLift.equiv.symm
  apply PLift.equiv.symm
  apply Sum.equivPSum.symm

instance {α: Sort*} {β: α -> Sort*} [IsFinite α]  [hb: ∀x, IsFinite (β x)] : IsFinite ((x: α) ×' β x) := by
  have := Fintype.ofIsFinite (PLift α)
  have : ∀x: PLift α, Fintype (PLift (β x.down)) := fun ⟨x⟩ =>
    Fintype.ofIsFinite (PLift (β x))
  apply IsFinite.ofEquiv' ((x : PLift α) × PLift (β x.down))
  apply Equiv.trans  _ Sigma.equivPSigma.symm
  apply PSigma.equivCongr PLift.equiv.symm
  intro x x₀ eq
  subst x₀
  apply Equiv.trans _ PLift.equiv.symm
  rfl

instance {α: Type*} {β: α -> Type*} [IsFinite α]  [hb: ∀x, IsFinite (β x)] : IsFinite ((x: α) × β x) := by
  have := Fintype.ofIsFinite (PLift α)
  have : ∀x: PLift α, Fintype (PLift (β x.down)) := fun ⟨x⟩ =>
    Fintype.ofIsFinite (PLift (β x))
  apply IsFinite.ofEquiv' ((x : PLift α) × PLift (β x.down))
  apply Sigma.equivCongr PLift.equiv.symm
  intro x x₀ eq
  subst x₀
  apply Equiv.trans _ PLift.equiv.symm
  rfl

instance {α: Type*} {β: Type*} [IsFinite α]  [IsFinite β] : IsFinite (α × β) := by
  have := Fintype.ofIsFinite α
  have := Fintype.ofIsFinite β
  exact inferInstance

instance {α: Sort*} {β: Sort*} [IsFinite α]  [IsFinite β] : IsFinite (α ×' β) := by
  apply IsFinite.ofEquiv' (PLift α × PLift β)
  apply Equiv.trans
  apply PProd.equivCongr
  apply PLift.equiv.symm
  apply PLift.equiv.symm
  apply Prod.equivPProd.symm

open Classical in
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
open Classical
instance {α: Sort*} {P: α -> Prop} [IsFinite α] : IsFinite (Subtype P) := by
  have := Fintype.ofIsFinite (PLift α)
  apply IsFinite.ofEquiv' (Subtype fun x: PLift α => P x.down)
  apply Subtype.congrEquiv _ _
  apply PLift.equiv.symm
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
  case inj =>
    intro ⟨x, hx⟩ ⟨y, hy⟩ eq
    dsimp at eq
    split at eq <;> split at eq <;> rename_i gx gy
    cases peqv.toFun_inj (Fin.addNat_inj eq)
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
    cases qeqv.toFun_inj eq
    rfl

instance {α: Sort*} {P Q: α -> Prop} [IsFinite (Subtype P)] [IsFinite (Subtype Q)] : IsFinite (Subtype (fun x => P x ∧ Q x)) := by
  apply IsFinite.ofEquiv' (Subtype fun x: Subtype P => Q x.val)
  apply Equiv.mk
  case toFun =>
    intro ⟨x, _, _⟩
    refine ⟨⟨x, ?_⟩, ?_⟩ <;> assumption
  case invFun =>
    intro ⟨⟨x, _⟩, _⟩
    refine ⟨x, ?_, ?_⟩ <;> assumption
  case leftInv => intro ⟨x, _, _⟩; rfl
  case rightInv => intro ⟨⟨x, _⟩, _⟩; rfl

instance [IsEmpty α] : IsFinite α := by
  apply IsFinite.intro 0
  apply empty_equiv_empty

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
  rw [IsFinite.card_eq_card, IsFinite.card_eq_card, card_eq']
