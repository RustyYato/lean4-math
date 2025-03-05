import Math.Data.Finset.Basic
import Math.Data.Trunc

class Fintype (α: Type*) where
  all: Finset α
  complete: ∀x, x ∈ all

namespace Finset

def univ (α: Type*) [Fintype α] : Finset α := Fintype.all
@[simp] def mem_univ {α: Type*} [Fintype α] : ∀x, x ∈ univ α := Fintype.complete

end Finset

namespace Fintype

variable {α β: Type*}

instance : Subsingleton (Fintype α) where
  allEq := by
    intro a b
    cases a with | mk a h =>
    cases b with | mk b g =>
    congr
    ext
    apply Iff.intro <;> intro
    apply g
    apply h

def card (α: Type*) [h: Fintype α] : Nat := h.all.card

def ofList (list: List α) (h: list.Nodup) (g: ∀x, x ∈ list) : Fintype α where
  all := {
    val := Multiset.mk list
    property := h
  }
  complete := g

def hrecOn {α: Type*}
  {motive: Fintype α -> Sort*}
  (mk: ∀all: List α, (h: all.Nodup) -> (g: ∀x, x ∈ all) -> motive (Fintype.ofList all h g))
  (eq: ∀(as bs: List α) (has: as.Nodup) (hbs: bs.Nodup) (gas: ∀x, x ∈ as) (gbs: ∀x, x ∈ bs),
    HEq (mk as has gas) (mk bs hbs gbs))
  (h: Fintype α) : motive h :=
  match h with
  | .mk ⟨all, nodup⟩ complete => by
    refine all.hrecOn (motive := fun all => (h: Multiset.Nodup all) -> (g: ∀x, Multiset.mem x all) -> motive ⟨⟨all, h⟩, g⟩) ?_ ?_ ?_ ?_
    intro a h g
    apply mk
    intro as bs as_perm_bs
    apply Function.hfunext
    show List.Nodup as = List.Nodup bs
    ext; exact List.Perm.nodup_iff as_perm_bs
    intro as_nodup bs_nodup nodup_eq
    apply Function.hfunext
    rw [Quotient.sound as_perm_bs]
    intro as_complete bs_complete  complete_eq
    apply eq

def recOnSubsingleton (α: Type*)
  {motive: Fintype α -> Sort*}
  [∀f, Subsingleton (motive f)]
  (mk: ∀all: List α, (h: all.Nodup) -> (g: ∀x, x ∈ all) -> motive (Fintype.ofList all h g))
  (h: Fintype α) : motive h :=
  match h with
  | .mk ⟨all, nodup⟩ complete => by
    apply all.recOnSubsingleton (motive := fun all => (h: Multiset.Nodup all) -> (g: ∀x, Multiset.mem x all) -> motive ⟨⟨all, h⟩, g⟩)
    intro a h g
    apply mk

@[induction_eliminator]
def induction (α: Type*)
  {motive: Fintype α -> Prop}
  (mk: ∀all: List α, (h: all.Nodup) -> (g: ∀x, x ∈ all) -> motive (Fintype.ofList all h g))
  (h: Fintype α) : motive h := recOnSubsingleton α mk h

def map {α: Type*}
  (mk: ∀all: List α, (h: all.Nodup) -> (g: ∀x, x ∈ all) -> Fintype β)
  (h: Fintype α) : Fintype β := by
  apply h.recOnSubsingleton
  apply mk

private def List.nodup_getElem_idxOf [BEq α] [LawfulBEq α] (as: List α) (x: α) (h: x ∈ as) (g: as.Nodup) :
  as[as.idxOf x]'(List.idxOf_lt_length h) = x := by
  apply Option.some.inj
  rw [←List.getElem?_eq_getElem]
  induction h with
  | head => rw [List.idxOf_cons, LawfulBEq.rfl, cond_true, List.getElem?_cons_zero]
  | tail _ _ ih =>
    rename_i a as h'
    rw [List.idxOf_cons, show (a == x) = false from ?_, cond_false, List.getElem?_cons_succ, ih]
    exact g.tail
    refine beq_false_of_ne ?_
    intro h
    exact g.head _ h' h

private def List.nodup_idxOf_getElem [BEq α] [LawfulBEq α] (as: List α) (x: Nat) (h: x < as.length) (g: as.Nodup) :
  as.idxOf as[x] = x := by
  induction x generalizing as with
  | zero =>
    cases  as
    contradiction
    rw [List.getElem_cons_zero, List.idxOf_cons, beq_self_eq_true, cond_true]
  | succ x ih =>
    cases as with
    | nil => contradiction
    | cons a as =>
    rw [List.getElem_cons_succ, List.idxOf_cons,
      beq_eq_false_iff_ne.mpr, cond_false, ih]
    exact g.tail
    have := Nat.lt_of_succ_lt_succ h
    intro h
    rw [h] at g
    exact g.head as[x] (by exact List.getElem_mem this) rfl

def equivFin (α: Type*) [DecidableEq α] [h: Fintype α] : Trunc (α ≃ Fin (card α)) := by
  apply h.recOnSubsingleton
  intro all nodup complete
  have card_eq : all.length = card α := by
    rw [Subsingleton.allEq h (Fintype.ofList all nodup complete)]
    rfl
  exact Trunc.mk {
    toFun a := ⟨all.idxOf a, by
      show _ < all.length
      exact List.idxOf_lt_length (complete a)⟩
    invFun i := all[i.cast card_eq]
    rightInv := by
      intro ⟨x, xLt⟩
      dsimp
      congr
      apply List.nodup_idxOf_getElem
      assumption
    leftInv := by
      intro a
      dsimp
      apply List.nodup_getElem_idxOf
      apply complete
      assumption
  }

def ofEquiv' (h: α ≃ β) [f: Fintype α] : Fintype β where
  all := f.all.map_emb h.toEmbedding
  complete := by
    intro x
    rw [Finset.mem_map_emb]
    exists h.symm x
    apply And.intro
    apply Fintype.complete
    apply Equiv.symm_coe

def ofEquiv (h: α ≃ β) [Fintype β] : Fintype α := ofEquiv' h.symm

def card_eq_of_equiv (h: α ≃ β) [ha: Fintype α] [hb: Fintype β] : card α = card β := by
  rw [Subsingleton.allEq ha (ofEquiv h)]
  induction hb with
  | mk bs bs_nodup bs_complete =>
  show List.length (List.map _ _) = _
  rw [List.length_map]
  rfl

def card_ne_zero_iff_nonempty [f: Fintype α] : card α ≠ 0 ↔ Nonempty α := by
  induction f with
  | mk all nodup complete =>
  show all.length ≠ 0 ↔ _
  apply Iff.intro
  intro h
  match all with
  | a::_ => exact ⟨a⟩
  intro ⟨a⟩ _
  match all with
  | [] => nomatch complete a

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
  induction fs with
  | mk all nodup complete =>
  have ⟨f'⟩ := List.collectNonempty f all
  refine ⟨?_⟩
  intro x
  apply f'
  apply complete

def Fintype.subsingleton [f: Fintype α] (h: card α ≤ 1) : Subsingleton α where
  allEq := by
    intro a b
    induction f with
    | mk all nodup complete =>
    match all with
    | [] => nomatch complete a
    | [x] =>
      cases List.mem_singleton.mp (complete a)
      cases List.mem_singleton.mp (complete b)
      rfl

instance : Fintype (Fin n) :=
  Fintype.ofList (List.finRange n) (by
    refine List.nodup_iff_getElem_inj.mpr ?_
    intro ⟨x, _⟩ ⟨y, _⟩ eq
    dsimp at eq
    simp at eq
    cases eq
    rfl) (by
    intro x
    apply (List.mem_ofFn _ _).mpr
    exists x)

def card_fin (n: Nat) : card (Fin n) = n := by
  apply List.length_ofFn

instance : Fintype Prop :=
  Fintype.ofList [False, True] (by simp) (by
    intro x
    simp; symm
    exact Classical.em x)

def card_prop : card Prop = 2 := rfl

instance : Fintype Bool :=
  Fintype.ofList [false, true] (by simp) (by intro x; simp)

def card_bool : card Bool = 2 := rfl

def fold [Fintype α] (f: α -> β -> β) (start: β) (h: ∀(a₀ a₁: α) (b: β), f a₀ (f a₁ b) = f a₁ (f a₀ b)) : β :=
  Fintype.all.val.fold f start h

def nat_not_fintype : Fintype Nat -> False := by
  intro f
  let m := f.fold max 0 (by
    intro a₀ a₁ b
    rw [
      ←Nat.max_assoc,
      Nat.max_comm a₀,
      Nat.max_assoc])
  have : ∀x, x ≤ m := by
    induction f with
    | mk all nodup complete =>
    intro x
    show x ≤ List.foldr _ _ _
    have mem := complete x
    clear m nodup complete
    induction mem with
    | head => apply Nat.le_max_left
    | tail =>
      apply flip Nat.le_trans
      apply Nat.le_max_right
      assumption
  exact Nat.not_lt_of_le (this (m + 1)) (Nat.lt_succ_self _)

instance [Inhabited α] [Subsingleton α] : Fintype α :=
  Fintype.ofList [default] (by simp) (by intro x; rw [Subsingleton.allEq x default]; apply List.Mem.head)

instance [IsEmpty α] : Fintype α :=
  Fintype.ofList [] (by simp) (by intro x; exact elim_empty x)

def card_unit : card Unit = 1 := rfl

def card_empty : card Empty = 0 := rfl

end Fintype
