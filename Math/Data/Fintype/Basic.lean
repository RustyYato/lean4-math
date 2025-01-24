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

def Fintype.embedding_of_card_le [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
  (h: card α ≤ card β) : α ↪ β := (Fin.embedFin h).congr equivFin.symm equivFin.symm

def Fintype.equiv_of_card_eq [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
  (h: card α = card β) : α ≃ β := equivFin.trans <| (Fin.equivOfEq h).trans equivFin.symm

def Fintype.recType
  {motive: ∀α: Type u, [Fintype α] -> Sort v}
  (nil: motive PEmpty)
  (cons: ∀α, [Fintype α] -> motive α -> motive (Option α))
  (equiv: ∀α β, [Fintype α] -> [Fintype β] -> motive α -> α ≃ β -> motive β)
  {α: Type u} [f: Fintype α] [DecidableEq α]: motive α :=
  match h:card α with
  | 0 => equiv _ _ nil (equiv_of_card_eq (α := PEmpty) (β := α) h.symm)
  | c + 1 =>
    let max: α := (f.equivFin (α := α)).symm ⟨0, h ▸ Nat.zero_lt_succ _⟩
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
    have : card { x // x ≠ equivFin.symm ⟨0, h ▸ Nat.zero_lt_succ _⟩ } < card α := by
      apply Nat.lt_of_succ_lt_succ
      rw [←Option.card_eq]
      apply Nat.lt_succ_of_le
      apply Nat.le_of_eq
      apply Fintype.eqCardOfEquiv
      assumption
    equiv _ _ (cons { x: α // x ≠ max } (recType nil cons equiv)) <| eqv
termination_by card α

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

def Fintype.existsEmbedding_iff_card_le [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]:
  Nonempty (α ↪ β) ↔ card α ≤ card β := by
  apply Fintype.ind (α := α) (motive := fun α _ => [DecidableEq α] -> ∀β, [Fintype β] -> [DecidableEq β] -> (Nonempty (α ↪ β) ↔ card α ≤ card β))
  case nil =>
    intro _ β _ _
    apply Iff.intro
    intro
    apply Nat.zero_le
    intro
    exact ⟨elim_empty, empty_inj _⟩
  case cons =>
    intro α _ ih _ β _ _
    have := decEqOfOption α inferInstance
    rw [Option.card_eq]
    apply Fintype.cases (α := β) (motive := fun β _ => [DecidableEq β] -> (Nonempty (Option α ↪ β) ↔ (card α).succ ≤ card β))
    case nil =>
      intro _
      apply Iff.intro
      intro ⟨h⟩
      have := h .none; contradiction
      intro; contradiction
    case cons =>
      intro β _ _
      have := decEqOfOption β inferInstance
      replace ih := ih β
      rw [Option.card_eq]
      apply Iff.intro
      intro ⟨emb⟩
      apply Nat.succ_le_succ
      apply ih.mp
      refine ⟨Embedding.ofOptionEmbed emb⟩
      intro h
      have ⟨h⟩ := ih.mpr (Nat.le_of_succ_le_succ h)
      refine ⟨Embedding.toOptionEmbed h⟩
    case equiv =>
      intro α β _ _ ih eqv _
      have := eqv.toEmbedding.DecidableEq
      rw [←Fintype.eqCardOfEquiv eqv]
      apply Iff.trans _ ih
      apply Iff.intro
      intro ⟨h⟩
      exact ⟨eqv.symm.toEmbedding.comp h⟩
      intro ⟨h⟩
      exact ⟨eqv.toEmbedding.comp h⟩
  case equiv =>
    intro α β _ _ ih eqv _ γ _ _
    rw [←Fintype.eqCardOfEquiv eqv]
    have := eqv.toEmbedding.DecidableEq
    apply Iff.trans _ (ih _)
    apply Iff.intro
    intro ⟨h⟩
    exact ⟨h.congr eqv.symm .refl⟩
    intro ⟨h⟩
    exact ⟨h.congr eqv .refl⟩

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
