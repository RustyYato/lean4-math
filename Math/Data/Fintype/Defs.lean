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

def Fintype.card_eq (a b: Fintype α) : a.card = b.card := by
  unfold card
  rw [List.Perm.length_eq]
  exact a.perm b

def Fintype.indexOf [DecidableEq α] (f: Fintype α) (x: α) : Fin (card α) where
  val := f.all.indexOf x
  isLt := by
    cases f with | mk all nodup compl =>
    unfold Fintype.card
    dsimp
    have : x ∈ all := compl _
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

def Fintype.embedFin [DecidableEq α] [f: Fintype α] : α ↪ Fin (card α) where
  toFun := f.indexOf
  inj := by
    intro x y eq
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

instance : GetElem (Fintype α) Nat α (fun _ n => n < Fintype.card α) where
  getElem f x p := f.all[x]

instance [f: Fintype α] [DecidableEq α] : IsFinite α := by
  exists Fintype.card α
  apply Fintype.embedFin

def Fintype.getElem_indexOf [DecidableEq α] {f: Fintype α} (x: α) : f[f.indexOf x] = x := by
  cases f with | mk all nodup complete =>
  show all[all.indexOf _]'_ = _
  have : x ∈ all := complete x
  suffices ∀(as: List α) (x: α) (h: x ∈ as), as[as.indexOf x]'(by
    induction h
    rw [List.indexOf_cons, cond_eq_if, if_pos]
    apply Nat.zero_lt_succ
    apply LawfulBEq.rfl
    rw [List.indexOf_cons, cond_eq_if]
    split
    apply Nat.zero_lt_succ
    apply Nat.succ_lt_succ
    assumption) = x by
    apply this
    assumption
  clear this complete nodup all x
  intro as x h
  apply Option.some.inj
  rw [←List.getElem?_eq_getElem]
  induction h
  rw [List.indexOf_cons, cond_eq_if, if_pos, List.getElem?_cons_zero]
  apply LawfulBEq.rfl
  rw [List.indexOf_cons, cond_eq_if]
  split
  rename_i h
  cases LawfulBEq.eq_of_beq h
  rw [List.getElem?_cons_zero]
  rw [List.getElem?_cons_succ]
  assumption

def Fintype.indexOf_getElem [DecidableEq α] {f: Fintype α} (x: Fin (card α)) : f.indexOf f[x] = x := by
  cases f with | mk all nodup complete =>
  unfold indexOf GetElem.getElem Fin.instGetElemFinVal GetElem.getElem instGetElemFintypeNatLtCard
  dsimp
  cases x with | mk x xLt =>
  congr
  unfold card Fintype.all at xLt
  dsimp at xLt
  dsimp
  suffices ∀(as: List α) (x: Fin as.length), as.Nodup -> as.indexOf as[x] = x by
    apply this _ ⟨x, _⟩
    assumption
    assumption
  clear xLt x complete nodup all
  intro as x nodup
  induction nodup with
  | nil =>
    have := x.isLt
    contradiction
  | cons nomem nodup ih =>
    cases x with | mk x xLt =>
    cases x with
    | zero =>
      erw [List.getElem_cons_zero, List.indexOf_cons, cond_eq_if, if_pos]
      apply LawfulBEq.rfl
    | succ x =>
    erw [List.getElem_cons_succ, List.indexOf_cons, cond_eq_if, if_neg]
    dsimp; congr; apply ih ⟨_, _⟩
    apply Nat.lt_of_succ_lt_succ
    assumption
    intro h
    replace h := LawfulBEq.eq_of_beq h
    apply nomem
    apply List.getElem_mem (Nat.lt_of_succ_lt_succ xLt)
    assumption

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

def Fintype.equivFin [f: Fintype α] [DecidableEq α] : α ≃ Fin f.card where
  toFun := f.indexOf
  invFun a := f[a]
  leftInv x := by
    dsimp
    erw [Fintype.getElem_indexOf]
  rightInv x := by
    dsimp
    erw [Fintype.indexOf_getElem]

def Fintype.equivOfEqCard [DecidableEq α] [DecidableEq β] {fa: Fintype α} {fb: Fintype β} (h: fa.card = fb.card) : α ≃ β := by
  apply (fa.equivFin).trans
  apply Equiv.trans _ (fb.equivFin).symm
  apply Fin.equivOfEq
  assumption

def Fintype.eqCardOfEquiv {fa: Fintype α} {fb: Fintype β} (h: α ≃ β) : fa.card = fb.card := by
  rw [Fintype.card_eq fb (fa.ofEquiv h)]
  show _  = (List.map _ _).length
  rw [List.length_map]
  rfl

def Fintype.ofEquiv_card_eq {fa: Fintype α} (h: α ≃ β) : (fa.ofEquiv h).card = fa.card := by
  unfold card all ofEquiv
  dsimp
  rw [List.length_map]
  rfl

instance {P: α -> Prop} [DecidablePred P] [f: Fintype α] : Decidable (∃x, P x) :=
  decidable_of_iff (∃x ∈ f.all, P x) <| by
    apply Iff.intro
    intro ⟨x, _, _⟩
    exists x
    intro ⟨x, _⟩
    exists x
    apply And.intro
    apply f.complete
    assumption
instance {P: α -> Prop} [DecidablePred P] [Fintype α] : Decidable (∀x, P x) := decidable_of_iff _ Decidable.not_exists_not
