import Math.Logic.Equiv.Basic
import Math.Data.Finset.Basic
import Math.Data.Set.Basic

class Fintype (α: Type _) where
  all: List α
  nodup: all.Nodup
  complete: ∀x, x ∈ all

def Finset.univ (α: Type _) [f: Fintype α] : Finset α where
  val := Multiset.mk f.all
  property := f.nodup

def Finset.mem_univ [f: Fintype α] : ∀x, x ∈ Finset.univ α := f.complete

instance [Fintype α] [DecidableEq α] : SetComplement (Finset α) where
  scompl f := Finset.univ _ \ f

def Finset.compl (α: Type _) [f: Fintype α] : Finset α where
  val := Multiset.mk f.all
  property := f.nodup

def Finset.mem_compl [Fintype α] [DecidableEq α] (f: Finset α) :
  ∀{x}, x ∈ fᶜ ↔ x ∉ f := by
  intro x
  show x ∈ Finset.univ _ \ f ↔ _
  simp [mem_sdiff, mem_univ]

@[simp]
def Finset.compl_compl [Fintype α] [DecidableEq α] (f: Finset α) : fᶜᶜ = f := by
  ext x
  simp [mem_compl]

namespace Fintype

def perm (a b: Fintype α) : a.all.Perm b.all := by
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

def card (α: Type _) [f: Fintype α] : Nat := f.all.length

def card_eq (a b: Fintype α) : a.card = b.card := by
  unfold card
  rw [List.Perm.length_eq]
  exact a.perm b

def idxOf [DecidableEq α] (f: Fintype α) (x: α) : Fin (card α) where
  val := f.all.idxOf x
  isLt := by
    cases f with | mk all nodup compl =>
    unfold card
    dsimp
    have : x ∈ all := compl _
    clear nodup compl
    induction this with
    | head _ =>
      rw [List.idxOf_cons]
      simp
    | tail _ _ ih =>
      rw [List.idxOf_cons]
      unfold cond
      split
      apply Nat.zero_lt_succ
      apply Nat.succ_lt_succ
      assumption

def embedFin [DecidableEq α] [f: Fintype α] : α ↪ Fin (card α) where
  toFun := f.idxOf
  inj' := by
    intro x y eq
    replace eq := Fin.mk.inj eq
    suffices ∀z, f.all[f.all.idxOf z]? = z by
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
      rw [List.idxOf_cons]
      simp
    | tail _ _ ih =>
      rw [List.idxOf_cons]
      unfold cond
      split
      rename_i h
      cases LawfulBEq.eq_of_beq h
      rw [List.getElem?_cons_zero]
      rw [List.getElem?_cons_succ]
      rw [ih]

instance : GetElem (Fintype α) Nat α (fun _ n => n < card α) where
  getElem f x p := f.all[x]

def getElem_idxOf [DecidableEq α] {f: Fintype α} (x: α) : f[f.idxOf x] = x := by
  cases f with | mk all nodup complete =>
  show all[all.idxOf _]'_ = _
  have : x ∈ all := complete x
  suffices ∀(as: List α) (x: α) (h: x ∈ as), as[as.idxOf x]'(by
    induction h
    rw [List.idxOf_cons, cond_eq_if, if_pos]
    apply Nat.zero_lt_succ
    apply LawfulBEq.rfl
    rw [List.idxOf_cons, cond_eq_if]
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
  rw [List.idxOf_cons, cond_eq_if, if_pos, List.getElem?_cons_zero]
  apply LawfulBEq.rfl
  rw [List.idxOf_cons, cond_eq_if]
  split
  rename_i h
  cases LawfulBEq.eq_of_beq h
  rw [List.getElem?_cons_zero]
  rw [List.getElem?_cons_succ]
  assumption

def idxOf_getElem [DecidableEq α] {f: Fintype α} (x: Fin (card α)) : f.idxOf f[x] = x := by
  cases f with | mk all nodup complete =>
  simp only [idxOf, GetElem.getElem]
  cases x with | mk x xLt =>
  congr
  dsimp only [List.get_eq_getElem]
  suffices ∀(as: List α) (x: Fin as.length), as.Nodup -> as.idxOf as[x] = x by
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
      erw [List.getElem_cons_zero, List.idxOf_cons, cond_eq_if, if_pos]
      apply LawfulBEq.rfl
    | succ x =>
    erw [List.getElem_cons_succ, List.idxOf_cons, cond_eq_if, if_neg]
    dsimp; congr; apply ih ⟨_, _⟩
    apply Nat.lt_of_succ_lt_succ
    assumption
    intro h
    replace h := LawfulBEq.eq_of_beq h
    apply nomem
    apply List.getElem_mem (Nat.lt_of_succ_lt_succ xLt)
    assumption

def ofEquiv {a b: Type _} (eq: a ≃ b) [f: Fintype b] : Fintype a where
  all := f.all.map eq.invFun
  nodup := by
    apply List.nodup_map
    apply eq.symm.inj
    exact f.nodup
  complete := by
    intro x
    apply List.mem_map.mpr
    exists eq.toFun x
    apply And.intro
    apply f.complete
    rw [eq.leftInv]

def ofEquiv' {a b: Type _} (eq: a ≃ b) [f: Fintype a] : Fintype b := ofEquiv eq.symm

def equivFin [f: Fintype α] [DecidableEq α] : α ≃ Fin f.card where
  toFun := f.idxOf
  invFun a := f[a]
  leftInv x := by
    dsimp
    erw [getElem_idxOf]
  rightInv x := by
    dsimp
    erw [idxOf_getElem]

def equivOfEqCard [DecidableEq α] [DecidableEq β] {fa: Fintype α} {fb: Fintype β} (h: fa.card = fb.card) : α ≃ β := by
  apply (fa.equivFin).trans
  apply Equiv.trans _ (fb.equivFin).symm
  apply Equiv.fin
  assumption

def eqCardOfEquiv {fa: Fintype α} {fb: Fintype β} (h: α ≃ β) : fa.card = fb.card := by
  rw [card_eq fb (fa.ofEquiv' h)]
  show _  = (List.map _ _).length
  rw [List.length_map]
  rfl

def ofEquiv_card_eq {fa: Fintype β} (h: α ≃ β) : (fa.ofEquiv h).card = fa.card := by
  unfold card all ofEquiv
  dsimp
  rw [List.length_map]
  rfl

def ofEquiv'_card_eq {fa: Fintype α} (h: α ≃ β) : (fa.ofEquiv' h).card = fa.card := by
  unfold ofEquiv'
  rw [ofEquiv_card_eq]

def IsEmpty [f: Fintype α] (h: card α = 0) : IsEmpty α where
  elim x := by
    match f with
    | .mk [] nodup complete =>
    have := complete x
    contradiction

def card_ne_zero_iff_nonempty [h:Fintype α] : card α ≠ 0 ↔ Nonempty α where
  mp x := ⟨h[0]⟩
  mpr x h :=
    have ⟨x⟩ := x
    (IsEmpty h).elim x

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

instance {β: α -> Type _} [Fintype α] [∀x, DecidableEq (β x)] : DecidableEq (∀x, β x) :=
  fun f g => if h:∀x, f x = g x then
    .isTrue (funext h)
  else
    .isFalse fun eq => (eq ▸ h) fun _ => rfl

instance [Fintype α] [DecidableEq β] : DecidableEq (α -> β) := inferInstance

instance [Fintype α] [DecidableEq β] [DecidableEq α] {f: α -> β} : Decidable (Function.Injective f) :=
  inferInstance

instance [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] {f: α -> β} : Decidable (Function.Surjective f) :=
  inferInstance

instance [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] {f: α -> β} : Decidable (Function.Bijective f) :=
  inferInstance

instance [Fintype β] [DecidableEq β] {f: α -> β} {g: β -> α} : Decidable (Function.IsLeftInverse f g) := by
  delta Function.IsLeftInverse
  exact inferInstance
instance [Fintype α][DecidableEq α] {f: α -> β} {g: β -> α} : Decidable (Function.IsRightInverse f g) := by
  delta Function.IsRightInverse
  exact inferInstance

end Fintype
