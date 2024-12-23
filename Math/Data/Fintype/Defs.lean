import Math.Data.List.Basic
import Math.Type.Finite

class Fintype (α: Type _) where
  all: List α
  nodup: all.Nodup
  complete: ∀x, x ∈ all

def Fintype.perm (a b: Fintype α) : a.all.Perm b.all := by
  cases a with | mk a anodup acomplete =>
  cases b with | mk b bnodup bcomplete =>
  apply List.MinCount.iff_perm.mpr
  intro x n
  cases n with
  | zero =>
  apply Iff.intro <;> (intro; apply List.MinCount.zero)
  | succ n =>
  cases n with
  | zero =>
  apply Iff.trans List.mem_iff_MinCount_one.symm
  apply Iff.trans _ List.mem_iff_MinCount_one
  apply Iff.intro <;> intro
  apply bcomplete
  apply acomplete
  | succ n =>
  apply Iff.intro <;> intro h
  have := List.minCount_of_nodup _ anodup h
  contradiction
  have := List.minCount_of_nodup _ bnodup h
  contradiction

def Fintype.card (α: Type _) [f: Fintype α] : Nat := f.all.length

instance [f: Fintype α] [DecidableEq α] : IsFinite α := by
  exists Fintype.card α
  apply Embedding.mk
  case toFun =>
    intro x
    refine ⟨f.all.indexOf x, ?_⟩
    cases f with | mk all nodup compl =>
    have : x ∈ all := compl _
    unfold Fintype.card
    dsimp
    clear nodup compl
    induction this with
    | head _ =>
      rw [List.indexOf_cons]
      simp
    | tail _ _ ih =>
      rw [List.indexOf_cons]
      unfold cond
      split
      apply Nat.zero_lt_succ
      apply Nat.succ_lt_succ
      assumption
  case inj =>
    intro x y eq
    dsimp at eq
    replace eq := Fin.mk.inj eq
    suffices ∀z, f.all[f.all.indexOf z]? = z by
      have opteq := this y
      rw [←eq, this x] at opteq
      exact Option.some.inj opteq
    clear eq x y
    intro z
    cases f with | mk all nodup compl =>
    have : z ∈ all := compl _
    simp
    clear nodup compl
    induction this with
    | head _ =>
      rw [List.indexOf_cons]
      simp
    | tail _ _ ih =>
      rw [List.indexOf_cons]
      unfold cond
      split
      rename_i h
      cases LawfulBEq.eq_of_beq h
      rw [List.getElem?_cons_zero]
      rw [List.getElem?_cons_succ]
      rw [ih]

def Fintype.card_eq (a b: Fintype α) : a.card = b.card := by
  unfold card
  rw [List.Perm.length_eq]
  exact a.perm b

def Fintype.ofEquiv {a b: Type _} (eq: a ≃ b) [f: Fintype a] : Fintype b where
  all := f.all.map eq.toFun
  nodup := by
    apply List.nodup_map
    apply eq.toFun_inj
    exact f.nodup
  complete := by
    intro x
    apply List.mem_map.mpr
    exists eq.invFun x
    apply And.intro
    apply f.complete
    rw [eq.rightInv]
