import Math.Data.Fintype.Fin
import Math.Data.Fintype.Pi
import Math.Data.Fintype.List
import Math.Data.Fintype.Sum
import Math.Data.Fintype.Prod
import Math.Data.Fintype.Subtype
import Math.Data.Fintype.Option
import Math.Data.Fintype.Prop

instance [Fintype α] [Fintype β] : Fintype (Except α β) := Fintype.ofEquiv Except.equivSum

instance : Fintype UInt8 := Fintype.ofEquiv UInt8.equivFin
instance : Fintype UInt16 := Fintype.ofEquiv UInt16.equivFin
instance : Fintype UInt32 := Fintype.ofEquiv UInt32.equivFin
instance : Fintype UInt64 := Fintype.ofEquiv UInt64.equivFin
instance : Fintype Char := Fintype.ofEquiv Char.equivSubtype
instance : Fintype Bool where
  all := [false, true]
  nodup := by decide
  complete := by decide

instance [Inhabited α] [Subsingleton α] : Fintype α where
  all := [default]
  nodup := List.Pairwise.cons nofun List.Pairwise.nil
  complete x := Subsingleton.allEq x default ▸ List.Mem.head _

instance [IsEmpty α] : Fintype α where
  all := []
  nodup := List.Pairwise.nil
  complete a := elim_empty a

instance [Decidable α] : Inhabited (Decidable α) where
  default := inferInstance

instance [Fintype α] : Fintype (PLift α) := Fintype.ofEquiv PLift.equiv
instance [Fintype α] : Fintype (ULift α) := Fintype.ofEquiv ULift.equiv

instance [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] : Fintype (α ↪ β) :=
  Fintype.ofEquiv Embedding.equivSubtype

instance [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] : Fintype (α ≃ β) :=
  Fintype.ofEquiv Equiv.equivSubtype

open Fintype in
def ULift.card_eq [f: Fintype α] [fu: Fintype (ULift α)] : card (ULift α) = card α := by
  apply Fintype.eqCardOfEquiv
  apply ULift.equiv
open Fintype in
def PLift.card_eq [f: Fintype α] [fu: Fintype (PLift α)] : card (PLift α) = card α := by
  apply Fintype.eqCardOfEquiv
  apply PLift.equiv

def Fintype.embedding_of_card_le [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
  (h: card α ≤ card β) : α ↪ β := (Fin.embedFin h).congr equivFin.symm equivFin.symm

def Fintype.equiv_of_card_eq [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
  (h: card α = card β) : α ≃ β := equivFin.trans <| (Fin.equivOfEq h).trans equivFin.symm

def Fintype.IsEmpty [f: Fintype α] (h: card α = 0) : IsEmpty α where
  elim x := by
    match f with
    | .mk [] nodup complete =>
    have := complete x
    contradiction

def Fintype.recType
  {motive: ∀α: Type u, [Fintype α] -> Sort v}
  (nil: motive PEmpty)
  (cons: ∀α, [Fintype α] -> motive α -> motive (Option α))
  (equiv: ∀α β, [Fintype α] -> [Fintype β] -> motive α -> α ≃ β -> motive β)
  {α: Type u} [f: Fintype α] [DecidableEq α]: motive α := by
  refine Nat.rec (motive := fun n => ∀α: Type u, [Fintype α] -> [DecidableEq α] -> card α = n -> motive α) ?_ ?_ (card α) _ rfl
  intro α _ _ eq
  have := Fintype.IsEmpty eq
  apply equiv _ _ nil (empty_equiv_empty _ _)
  intro n ih α f _ eq
  -- choose an arbitrary value from the fintype
  have max: α := f.all[0]'(by
    unfold card at eq
    erw [eq]
    apply Nat.zero_lt_succ)
  let eqv: Option {x: α // x ≠ max } ≃ α := {
    toFun
    | .some x => x.val
    | .none => max
    invFun x := if g:x = max then .none else .some ⟨x, g⟩
    leftInv := by
      intro x
      cases x <;> dsimp
      rw [dif_pos rfl]
      rw [dif_neg]
    rightInv := by
      intro x
      dsimp
      cases decEq x max <;> rename_i g
      rw [dif_neg g]
      rw [dif_pos g]
      symm; assumption
  }
  have : card { x // x ≠ max } = n := by
    apply Nat.succ.inj
    rw [←Option.card_eq, Fintype.eqCardOfEquiv eqv]
    assumption
  exact equiv _ _ (cons { x: α // x ≠ max } (ih _ this)) <| eqv

def Fintype.ind
  {motive: ∀α: Type u, [Fintype α] -> Prop}
  (nil: motive PEmpty)
  (cons: ∀α, [Fintype α] -> motive α -> motive (Option α))
  (equiv: ∀α β, [Fintype α] -> [Fintype β] -> motive α -> α ≃ β -> motive β)
  (α: Type u) [Fintype α] [DecidableEq α]: motive α := recType nil cons equiv

def Fintype.cases
  {motive: ∀α: Type u, [Fintype α] -> Prop}
  (nil: motive PEmpty)
  (cons: ∀α, [Fintype α] -> motive (Option α))
  (equiv: ∀α β, [Fintype α] -> [Fintype β] -> motive α -> α ≃ β -> motive β)
  (α: Type u) [Fintype α] [DecidableEq α]: motive α := recType nil (fun α _ _ => cons α) equiv

private def decEqOfOption (α: Type _) : DecidableEq (Option α) -> DecidableEq α :=
  fun _ => Option.embed.DecidableEq

def Fintype.existsEmbedding_iff_card_le
  {α: Type u} {β: Type v}
  [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]:
  Nonempty (α ↪ β) ↔ card α ≤ card β := by
  apply flip Iff.intro
  intro h; exact ⟨Fintype.embedding_of_card_le h⟩
  revert α
  apply Fintype.ind (α := β) (motive := fun β _ => [DecidableEq β] -> ∀α, [Fintype α] -> [DecidableEq α] -> (Nonempty (α ↪ β) -> card α ≤ card β))
  case a.nil =>
    intro _ β _ _
    intro ⟨h⟩
    cases g:card β
    apply Nat.zero_le
    have := Fintype.equivFin (α := β)
    rw [g] at this
    have := h (this.symm 0)
    contradiction
  case a.cons =>
    intro α _ ih _ β _ _
    have := decEqOfOption α inferInstance
    rw [Option.card_eq]
    intro ⟨h⟩
    match g:card β with
    | 0 => apply Nat.zero_le
    | c + 1 =>
      apply Nat.succ_le_succ
      replace ih := ih (ULift (Fin c))
      rw [ULift.card_eq, Fin.card_eq (n := c) inferInstance] at ih
      apply ih
      refine ⟨Embedding.ofOptionEmbed ?_⟩
      refine (Embedding.congr ?_ Option.swapULift .refl)
      apply h.comp
      refine Embedding.congr ?_ ULift.equiv.symm Fintype.equivFin.symm
      rw [g]; apply Option.equivFinSucc.symm.toEmbedding
  case a.equiv =>
    intro α β _ _ ih eqv _ γ _ _
    rw [←Fintype.eqCardOfEquiv eqv]
    have := eqv.toEmbedding.DecidableEq
    intro ⟨h⟩
    apply ih
    refine ⟨h.congr .refl eqv.symm⟩

private def List.collectNonempty [DecidableEq α] {β: α -> Sort*}
  (f: ∀x: α, Nonempty (β x)) : ∀as: List α, Nonempty (∀x: α, x ∈ as -> β x) := by
  intro as
  induction as with
  | nil => exact ⟨nofun⟩
  | cons a as ih =>
    obtain ⟨ih⟩ := ih
    obtain ⟨fa⟩ := f a
    refine ⟨?_⟩
    intro x mem
    refine if h:x = a then ?_ else ?_
    rw [h]
    assumption
    apply ih
    cases mem
    contradiction
    assumption

def Fintype.axiomOfChoice [DecidableEq α] {β: α -> Sort*} [fs: Fintype α] (f: ∀x: α, Nonempty (β x)) : Nonempty (∀x, β x) := by
  have ⟨f'⟩ := List.collectNonempty f fs.all
  refine ⟨?_⟩
  intro x
  apply f'
  apply fs.complete
