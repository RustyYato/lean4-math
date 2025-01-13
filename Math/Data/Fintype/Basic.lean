import Math.Data.Fintype.Fin
import Math.Data.Fintype.Pi
import Math.Data.Fintype.List
import Math.Data.Fintype.Sum
import Math.Data.Fintype.Prod
import Math.Data.Fintype.Subtype
import Math.Data.Fintype.Option

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

def Fintype.existsEmbedding_iff_card_le' :
  Nonempty (Fin n ↪ Fin m) ↔ n ≤ m := by
  apply Iff.symm (Iff.intro _ _)
  · intro h
    apply Nonempty.intro
    apply Embedding.mk _ _
    intro x
    apply x.castLE _
    assumption
    intro _ _ eq
    dsimp at eq
    exact Fin.val_inj.mp (Fin.mk.inj eq)
  induction m generalizing n with
  | zero =>
    intro ⟨emb⟩
    cases n
    apply Nat.le_refl
    exact (emb 0).elim0
  | succ m ih =>
    intro ⟨emb⟩
    cases n
    apply Nat.zero_le
    rename_i n
    apply Nat.succ_le_succ
    apply ih
    apply Nonempty.intro
    · apply Embedding.mk _ _
      intro x
      let out := emb.toFun (x.castLE (Nat.le_succ _))
      if h:out = Fin.last m then
        let m' := emb.toFun (Fin.last n)
        have : m' ≠ Fin.last m := by
          rw [←h]
          intro g
          have := emb.inj g
          have : n = x.val := Fin.val_inj.mpr this
          have : n < n := by
            conv => { lhs; rw [this] }
            exact x.isLt
          exact Nat.lt_irrefl _ this
        apply Fin.mk m'
        apply Nat.lt_of_le_of_ne
        apply Nat.le_of_lt_succ
        exact m'.isLt
        intro g
        apply this
        apply Fin.val_inj.mp
        exact g
      else
        apply Fin.mk out
        apply Nat.lt_of_le_of_ne
        apply Nat.le_of_lt_succ
        exact out.isLt
        intro g
        apply h
        apply Fin.val_inj.mp
        exact g
      intro x y eq
      dsimp at eq
      split at eq <;> split at eq <;> rename_i h g
      apply Fin.val_inj.mp
      have := Fin.val_inj.mpr (emb.inj (h.trans g.symm))
      exact this
      have : n = y.val := Fin.val_inj.mpr <| emb.inj <| Fin.val_inj.mp <| Fin.mk.inj eq
      have : n < n := by
        conv => { lhs; rw [this] }
        exact y.isLt
      have := Nat.lt_irrefl _ this
      contradiction
      have : n = x.val := Fin.val_inj.mpr <| emb.inj <| Fin.val_inj.mp <| Fin.mk.inj eq.symm
      have : n < n := by
        conv => { lhs; rw [this] }
        exact x.isLt
      have := Nat.lt_irrefl _ this
      contradiction
      have := emb.inj <| Fin.val_inj.mp <| Fin.mk.inj eq
      unfold Fin.castLE at this
      exact Fin.val_inj.mp (Fin.mk.inj this)

def Fintype.existsEmbedding_iff_card_le [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] :
  Nonempty (α ↪ β) ↔ card α ≤ card β := by
  apply Iff.trans _ Fintype.existsEmbedding_iff_card_le'
  apply Iff.intro
  intro ⟨emb⟩
  apply Nonempty.intro
  apply Embedding.congr
  assumption
  apply Fintype.equivFin
  apply Fintype.equivFin
  intro ⟨emb⟩
  apply Nonempty.intro
  apply Embedding.congr
  assumption
  apply Fintype.equivFin.symm
  apply Fintype.equivFin.symm

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
