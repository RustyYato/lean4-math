import Math.Data.QuotLike.Basic
import Math.Type.Notation
import Math.Data.List.Basic
import Math.Function.Basic
import Math.Relation.Basic
import Math.AxiomBlame

def Multiset (α: Type*) := Quotient (List.isSetoid α)

namespace Multiset

def mk : List α -> Multiset α := Quotient.mk _
instance : QuotientLike (List.isSetoid α) (Multiset α) where

local notation "⟦" a "⟧" => mk a

@[cases_eliminator]
def ind {motive: Multiset α -> Prop} : (mk: ∀x, motive ⟦x⟧) -> ∀x, motive x := Quotient.ind
@[cases_eliminator]
def ind₂ {motive: Multiset α -> Multiset α -> Prop} : (mk: ∀x y, motive ⟦x⟧ ⟦y⟧) -> ∀x y, motive x y := Quotient.ind₂
@[cases_eliminator]
def ind₃ {motive: Multiset α -> Multiset α -> Multiset α -> Prop} : (mk: ∀a b c, motive ⟦a⟧ ⟦b⟧ ⟦c⟧) -> ∀a b c, motive a b c := by
  intro  h a b c
  cases a, b; cases c
  apply h
@[cases_eliminator]
def ind₄ {motive: Multiset α -> Multiset α -> Multiset α -> Multiset α -> Prop} : (mk: ∀a b c d, motive ⟦a⟧ ⟦b⟧ ⟦c⟧ ⟦d⟧) -> ∀a b c d, motive a b c d := by
  intro  h a b c d
  cases a, b; cases c, d
  apply h

instance : EmptyCollection (Multiset α) := ⟨⟦[]⟧⟩

def toList : Multiset α -> List α := unwrapQuot

def mem (x: α) : Multiset α -> Prop := Quot.lift (x ∈ ·) <| by
  intro x y eq
  exact propext eq.mem_iff

instance : Membership α (Multiset α) := ⟨flip mem⟩

def MinCountBy (P: α -> Prop) (n: Nat) : Multiset α -> Prop := Quot.lift (List.MinCountBy P · n) <| by
  intro x y eq
  dsimp
  apply propext
  apply Iff.intro
  apply List.MinCountBy.of_perm eq
  apply List.MinCountBy.of_perm eq.symm

def MinCount (x: α) (n: Nat) : Multiset α -> Prop := Quot.lift (List.MinCount · x n) <| by
  intro x y eq
  dsimp
  exact propext eq.min_count_iff

def min_count_eq_min_count_by {as: Multiset α} {x: α} {n: Nat} :
  (as.MinCount x n) = (as.MinCountBy (· = x) n) := by
  cases as
  rfl

@[simp]
def mk_mem (x: α) (as: List α) : (x ∈ ⟦as⟧) = (x ∈ as) := rfl

def cons (x: α) : Multiset α -> Multiset α := Quot.lift (⟦List.cons x ·⟧) <| by
  intro x y eq
  apply quot.sound
  apply List.Perm.cons
  assumption

infixr:67 " ::ₘ " => cons

instance : Insert α (Multiset α) := ⟨.cons⟩
instance : Singleton α (Multiset α) := ⟨(.cons · ∅)⟩

@[induction_eliminator]
def induction {motive: Multiset α -> Prop}
  (nil: motive ∅)
  (cons: ∀a as, motive as -> motive (a::ₘas)):
  ∀m, motive m := by
  intro m
  cases m with | mk m =>
  induction m with
  | nil => exact nil
  | cons _ _ ih => exact cons _ _ ih

@[simp]
def mk_cons (x: α) (as: List α) : x ::ₘ ⟦as⟧ = ⟦x::as⟧ := rfl

@[simp]
def mem_cons {a: α} {as: Multiset α} : ∀{x}, x ∈ a::ₘas ↔ x = a ∨ x ∈ as := by
  intro x
  cases as with | mk as =>
  simp

def cases_mem_cons
  {x: α}
  {motive: ∀(a: α) (as: Multiset α), x ∈ a::ₘas -> Prop}
  (head: ∀{as}, motive x as (mem_cons.mpr (.inl rfl)))
  (tail: ∀{a} {as} (mem: x ∈ as), motive a as (mem_cons.mpr (.inr mem))):
  ∀{a as} (mem: x ∈ (a::ₘas)), motive a as mem := by
  intro a as mem
  cases as
  cases mem
  apply head
  rename_i mem
  apply tail mem

def rec' {motive: Multiset α -> Sort _}
  (nil: motive ∅) (cons: ∀a as, motive as -> motive (a::ₘas)) :
  ∀ms, motive ⟦ms⟧ := by
  intro ms
  match ms with
  | [] => exact nil
  | m::ms =>
    show motive (m::ₘ⟦ms⟧)
    apply cons
    apply rec'
    assumption
    assumption

private
def rec_prf_cons {x as bs}
  {motive: Multiset α -> Sort u}
  {cons: ∀a as, motive as -> motive (a::ₘas)}
  (as_eq_bs: as = bs)
  (mas: motive as)
  (mbs: motive bs):
  HEq mas mbs -> HEq (cons x as mas) (cons x bs mbs) := by
  intro eq
  subst bs
  cases eq
  rfl

def rec {motive: Multiset α -> Sort _}
  (nil: motive ∅) (cons: ∀a as, motive as -> motive (a::ₘas))
  (swap: ∀a a' as mas, HEq (cons a _ (cons a' as mas)) (cons a' _ (cons a as mas))) :
  ∀ms, motive ms := by
  intro ms
  apply Quot.hrecOn ms
  case f =>
    intro ms
    apply rec' <;> assumption
  intro a b a_perm_b
  induction a_perm_b with
  | nil => rfl
  | trans _ _ aih bih => exact aih.trans bih
  | cons _ _ ih =>
    unfold rec'
    dsimp
    apply rec_prf_cons
    apply quot.sound
    assumption
    assumption
  | swap =>
    unfold rec' rec'
    dsimp
    rename_i x y as
    apply swap (a := y) (a' := x) (as := ⟦as⟧)

def append : Multiset α -> Multiset α -> Multiset α := by
  apply Quotient.lift₂ (⟦· ++ ·⟧)
  intro a b c d ac bd
  apply quot.sound
  apply List.Perm.append <;> assumption

instance : Append (Multiset α) := ⟨.append⟩

@[simp]
def mk_append (as bs: List α) : ⟦as⟧ ++ ⟦bs⟧ = ⟦as ++ bs⟧ := rfl

@[simp]
def mem_append {as bs: Multiset α} : ∀{x}, x ∈ as ++ bs ↔ x ∈ as ∨ x ∈ bs := by
  intro x
  cases as, bs
  simp

def append_comm (as bs: Multiset α) : as ++ bs = bs ++ as := by
  cases as, bs
  simp
  apply quot.sound
  apply List.perm_append_comm
def append_assoc (as bs cs: Multiset α) : as ++ bs ++ cs = as ++ (bs ++ cs) := by
  cases as, bs, cs
  simp

def map {β: Type _} (f: α -> β) (as: Multiset α) : Multiset β := by
  apply Quot.lift (⟦·.map f⟧) _ as
  intro a b h
  apply quot.sound
  induction h with
  | nil => apply List.Perm.nil
  | trans _ _ aih bih => apply aih.trans bih
  | cons a _ ih =>
    apply List.Perm.cons
    assumption
  | swap => apply List.Perm.swap

@[simp]
def mk_map (a: List α) (f: α -> β) : ⟦a⟧.map f = ⟦a.map f⟧ := rfl

def flatten (as: Multiset (Multiset α)) : Multiset α := by
  apply Quot.lift _ _ as
  intro xs
  exact xs.foldr (· ++ ·) ∅
  intro a b aeqb
  induction aeqb with
  | nil => rfl
  | cons a as ih =>
    unfold List.foldr
    congr
  | trans _ _ aih bih => rw [aih, bih]
  | swap a as ih =>
    unfold List.foldr
    unfold List.foldr
    rw [←append_assoc, ←append_assoc, append_comm a]

@[simp]
def mk_flatten (as: List (List α)) : ⟦as.map (⟦·⟧)⟧.flatten = ⟦as.flatten⟧ := by
  unfold flatten
  show List.foldr _ _ _ = _
  rw [List.foldr_map]
  induction as with
  | nil => rfl
  | cons a as ih => simp [ih]

def mk_flatten' (as: List (Multiset α)) : ⟦as⟧.flatten = ⟦(as.map unwrapQuot).flatten⟧ := by
  rw [←mk_flatten]
  congr
  rw [List.map_map, List.map_id'']
  apply mk_unwrapQuot

def flatMap {β: Type _} (f: α -> Multiset β) (as: Multiset α) : Multiset β :=
  (as.map f).flatten

def flatten_cons (a: Multiset α) (as: Multiset (Multiset α)) : (a::ₘas).flatten = a ++ as.flatten := by
  quot_ind (a as)
  rfl

@[simp]
def mk_flatMap (as: List α) (f: α -> List β) : ⟦as⟧.flatMap (fun x => ⟦f x⟧) = ⟦as.flatMap f⟧ := by
  unfold flatMap
  rw [mk_map]
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp [ih, ←mk_cons, flatten_cons]

def mk_flatMap' (as: List α) (f: α -> Multiset β) : ⟦as⟧.flatMap f = ⟦as.flatMap (unwrapQuot ∘ f)⟧ := by
  rw [←mk_flatMap]
  congr
  funext
  symm
  apply mk_unwrapQuot

def flatMap_cons (a: α) (as: Multiset α) (f: α -> Multiset β) : (a::ₘas).flatMap f = f a ++ as.flatMap f := by
  cases as
  simp
  rfl

def map_append (as bs: Multiset α) (f: α -> β) : (as ++ bs).map f = as.map f ++ bs.map f := by
  cases as, bs
  simp

def map_map (ms: Multiset α) (f: α -> β) (g: β -> γ) : (ms.map f).map g = ms.map (g ∘ f) := by
  quot_ind ms
  apply quot.sound
  simp
  induction ms with
  | nil => apply List.Perm.nil
  | cons m ms ih =>
    apply List.Perm.cons
    apply ih

def flatMap_map (ms: Multiset α) (f: α -> Multiset β) (g: β -> γ) : (ms.flatMap f).map g = ms.flatMap (fun x => (f x).map g) := by
  cases ms with | mk ms =>
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    simp [flatMap_cons, ←mk_cons, map_append]
    congr

theorem flatMap_congr {ms : Multiset α} {f f': α → Multiset β}
  (hf : ∀ a ∈ ms, (f a) = (f' a)) : ms.flatMap f = ms.flatMap f' := by
  cases ms with | mk ms =>
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    simp [←mk_cons, flatMap_cons]
    congr 1
    apply hf
    apply List.Mem.head
    apply ih
    intro a ha
    apply hf
    apply List.Mem.tail
    assumption

theorem flatMap_hcongr {β' : Type v} {m : Multiset α} {f : α → Multiset β} {f' : α → Multiset β'}
    (h : β = β') (hf : ∀ a ∈ m, HEq (f a) (f' a)) : HEq (m.flatMap f) (m.flatMap f') := by
  subst h
  simp only [heq_eq_eq] at hf
  simp [flatMap_congr hf]

instance [DecidableEq α] : DecidableEq (Multiset α) := Quotient.decidableEq

def of_count_cons {x a: α} {as: Multiset α} {n: Nat} :
  (a::ₘas).MinCount x n -> as.MinCount x n ∨ (n ≠ 0 ∧ x = a ∧ as.MinCount a n.pred) := by
  quot_ind as
  intro h
  cases h
  left
  assumption
  right
  apply And.intro
  exact Nat.noConfusion
  apply And.intro
  symm; assumption
  dsimp
  rename_i h
  subst x
  assumption

def MinCountBy.zero : MinCountBy P 0 ms := by
  quot_ind ms
  apply List.MinCountBy.zero

def MinCountBy.nil {P: α -> Prop} : MinCountBy P 0 ∅ := List.MinCountBy.nil

def MinCountBy.head : P x -> MinCountBy P n ms -> MinCountBy P n.succ (x::ₘms) := by
  quot_ind ms
  intro c
  apply List.MinCountBy.head
  assumption

def MinCountBy.pop_head : P x -> MinCountBy P n.succ (x::ₘms) -> MinCountBy P n ms := by
  quot_ind ms
  intro c
  intro h
  cases h
  rename_i h
  apply h.reduce
  apply Nat.le_succ
  assumption

def MinCountBy.cons : MinCountBy P n ms -> MinCountBy P n (m::ₘms) := by
  quot_ind ms
  intro c
  apply List.MinCountBy.cons
  assumption

def MinCountBy.reduce : MinCountBy P n ms ->  ∀m ≤ n, MinCountBy P m ms := by
  quot_ind ms
  intro c
  apply List.MinCountBy.reduce
  assumption

def MinCount.nil : MinCount x 0 ∅ := List.MinCountBy.nil

def MinCount.zero : MinCount x 0 ms := by
  quot_ind ms
  apply List.MinCount.zero

def MinCount.head : MinCount x n ms -> MinCount x n.succ (x::ₘms) := by
  quot_ind ms
  intro c
  apply List.MinCount.head
  assumption

def MinCount.cons : MinCount x n ms -> MinCount x n (m::ₘms) := by
  quot_ind ms
  intro c
  apply List.MinCountBy.cons
  assumption

def MinCount.pop_head : MinCount a (n + 1) (a::ₘas) -> MinCount a n as := by
  cases as
  apply List.MinCount.pop_head

def MinCount.reduce : MinCount P n ms ->  ∀m ≤ n, MinCount P m ms := MinCountBy.reduce

@[induction_eliminator]
def MinCountBy.ind {P: α -> Prop} {motive: ∀(n: Nat) (ms: Multiset α), MinCountBy P n ms -> Prop}
  (nil: motive 0 ∅ MinCountBy.nil)
  (cons: ∀a as n h,  motive n as h -> motive n (ms := a::ₘas) h.cons)
  (head: ∀a as n h (pa: P a), motive n as h -> motive n.succ (a::ₘas) (h.head pa)):
  ∀{n} {as: Multiset α} (h: MinCountBy P n as), motive n as h := by
  intro n as h
  cases as
  induction h
  assumption
  rename_i a as n _ _
  apply cons a ⟦as⟧ n
  assumption
  rename_i a as n _ _ _
  apply head a ⟦as⟧ n
  assumption
  assumption

@[cases_eliminator]
def MinCountBy.cases {P: α -> Prop} {motive: ∀(n: Nat) (ms: Multiset α), MinCountBy P n ms -> Prop}
  (nil: motive 0 ∅ MinCountBy.nil)
  (cons: ∀a as n (h: MinCountBy P n as), motive n (a::ₘas) h.cons)
  (head: ∀a as n (h: MinCountBy P n as) (pa: P a), motive n.succ (a::ₘas) (h.head pa)):
  ∀{n: Nat} {as: Multiset α} (h: MinCountBy P n as), motive n as h := by
  intro n as h
  induction h
  exact nil
  apply cons
  assumption
  apply head
  assumption
  assumption

def MinCountBy.casesCons {P: α -> Prop} {motive: ∀(n: Nat) (m: α) (ms: Multiset α), MinCountBy P n (m::ₘms) -> Prop}
  (cons: ∀a as n (h: MinCountBy P n as), motive n a as h.cons)
  (head: ∀a as n (h: MinCountBy P n as) (pa: P a), motive n.succ a as (h.head pa)):
  ∀{n: Nat} {a: α} {as: Multiset α} (h: MinCountBy P n (a::ₘas)), motive n a as h := by
  intro n a as h
  cases as
  replace h : List.MinCountBy _ _ _ := h
  cases h
  apply cons
  assumption
  apply head
  assumption
  assumption

@[induction_eliminator]
def MinCount.ind {x: α} {motive: ∀(n: Nat) (ms: Multiset α), MinCount x n ms -> Prop}
  (nil: motive 0 ∅ MinCount.nil)
  (cons: ∀a as n h,  motive n as h -> motive n (ms := a::ₘas) h.cons)
  (head: ∀as n h, motive n as h -> motive n.succ (x::ₘas) h.head):
  ∀{n} {as: Multiset α} (h: MinCount x n as), motive n as h := by
  intro n as h
  cases as
  apply MinCountBy.ind nil cons
  intros a as n h p ih
  subst x
  apply head
  assumption

@[cases_eliminator]
def MinCount.cases {x: α} {motive: ∀(n: Nat) (ms: Multiset α), MinCount x n ms -> Prop}
  (nil: motive 0 ∅ MinCount.nil)
  (cons: ∀a as n (h: MinCount x n as), motive n (ms := a::ₘas) h.cons)
  (head: ∀as n (h: MinCount x n as), motive n.succ (x::ₘas) h.head):
  ∀{n: Nat} {as: Multiset α} (h: MinCount x n as), motive n as h := by
  intro n as h
  induction h
  exact nil
  apply cons
  assumption
  apply head
  assumption

def MinCount.casesCons {x: α} {motive: ∀(n: Nat) (m: α) (ms: Multiset α), MinCount x n (m::ₘms) -> Prop}
  (cons: ∀a as n (h: MinCount x n as), motive n a as h.cons)
  (head: ∀as n (h: MinCount x n as), motive n.succ x as h.head):
  ∀{n: Nat} {a: α} {as: Multiset α} (h: MinCount x n (a::ₘas)), motive n a as h := by
  apply MinCountBy.casesCons
  assumption
  intros
  subst x
  apply head
  assumption

def Pairwise (P: α -> α -> Prop) [Relation.IsSymmetric P] : Multiset α -> Prop := by
  apply Quotient.lift (List.Pairwise P)
  suffices ∀a b, a ≈ b -> List.Pairwise P a -> List.Pairwise P b by
    intro a b eq
    ext; apply Iff.intro
    apply this; assumption
    apply this; apply List.Perm.symm; assumption
  intro a b eq p
  induction eq with
  | nil => apply List.Pairwise.nil
  | cons a perm ih =>
    rcases p; rename_i p c
    apply List.Pairwise.cons
    intro a mem
    apply c
    apply perm.mem_iff.mpr
    assumption
    apply ih
    assumption
  | trans _ _ ih₀ ih₁ =>
    apply ih₁
    apply ih₀
    assumption
  | swap =>
    cases p; rename_i p c₀
    cases p; rename_i p c₁
    apply List.Pairwise.cons
    intro x mem
    cases mem
    apply Relation.symm
    apply c₀
    apply List.Mem.head
    apply c₁
    assumption
    apply List.Pairwise.cons
    intro x mem
    apply c₀
    apply List.Mem.tail
    assumption
    assumption

def Pairwise.nil {P: α -> α -> Prop} {_: Relation.IsSymmetric P} : Pairwise P ∅ :=
  List.Pairwise.nil

def Pairwise.cons {P: α -> α -> Prop} {_: Relation.IsSymmetric P}
  (h: Pairwise P as)
  (g: ∀x ∈ as, P a x)
   : Pairwise P (a::ₘas) := by
  cases as with | mk as =>
  apply List.Pairwise.cons <;> assumption

def Pairwise.head {P: α -> α -> Prop} {_: Relation.IsSymmetric P}
  (h: Pairwise P (a::ₘas))
   : ∀x ∈ as, P a x := by
  cases as with | mk as =>
  cases h
  assumption

def Pairwise.tail {P: α -> α -> Prop} {_: Relation.IsSymmetric P}
  (h: Pairwise P (a::ₘas))
   : Pairwise P as := by
  cases as with | mk as =>
  cases h
  assumption

def cons_comm (a b: α) (cs: Multiset α): a ::ₘ b ::ₘ cs = b ::ₘ a ::ₘ cs := by
  cases cs with | mk cs =>
  apply Quotient.sound
  apply List.Perm.swap

instance (P: α -> Prop) [DecidablePred P] (a: Multiset α) : Decidable (∃x ∈ a, P x) := by
  apply Quotient.recOnSubsingleton a (motive := _)
  intro a
  show Decidable (∃x ∈ a, P x)
  infer_instance
instance (P: α -> Prop) [DecidablePred P] (a: Multiset α) : Decidable (∀x ∈ a, P x) :=
  decidable_of_iff (¬∃x ∈ a, ¬P x) (by
    apply Iff.intro
    intro h
    replace h := not_exists.mp h
    intro x mem
    exact Decidable.not_not.mp <| (not_and.mp (h x)) mem
    intro h ⟨x, mem, nPx⟩
    exact nPx (h _ mem))

instance [DecidableEq α] (x: α) (s: Multiset α) : Decidable (x ∈ s) := by
  apply Quotient.recOnSubsingleton s (motive := fun _ => _)
  intro as
  show Decidable (x ∈ as)
  infer_instance

def mem_head (a: α) (as: Multiset α) : a ∈ (a::ₘas) := by
  cases as
  apply List.Mem.head

def mem_tail (x a: α) (as: Multiset α) : x ∈ as -> x ∈ (a::ₘas) := by
  cases as
  apply List.Mem.tail

def erase [DecidableEq α] (x: α) (as: Multiset α) : Multiset α := by
  apply as.lift (fun as => ⟦as.erase x⟧)
  intro a b eq
  apply Quotient.sound
  induction eq with
  | nil => apply List.Perm.nil
  | cons c perm ih =>
    unfold List.erase
    split
    assumption
    apply List.Perm.cons
    assumption
  | trans _ _ ih₀ ih₁ => exact ih₀.trans ih₁
  | swap a b xs =>
    unfold List.erase List.erase
    cases h:a == x <;> cases g:b == x <;> dsimp
    apply List.Perm.swap
    apply List.Perm.refl
    apply List.Perm.refl
    cases LawfulBEq.eq_of_beq h
    cases LawfulBEq.eq_of_beq g
    apply List.Perm.refl

def erase_empty [DecidableEq α] (x: α) : erase x ∅ = ∅ := rfl
def erase_cons [DecidableEq α] (x a: α) (as: Multiset α) : (a::ₘas).erase x = if x = a then as else a::ₘ(as.erase x) := by
  cases as
  show ⟦List.erase (a::_) x⟧ = _
  rw [List.erase]
  split <;> rename_i h
  rw [if_pos]
  symm; apply LawfulBEq.eq_of_beq
  assumption
  rw [if_neg]
  rfl
  intro h
  subst x
  rw [LawfulBEq.rfl] at h
  contradiction

def count_by_erase [DecidableEq α] (x: α) (as: Multiset α) (h: x ∉ as ∨ ¬P x) : as.MinCountBy P n ↔ (as.erase x).MinCountBy P n := by
  induction as generalizing n with
  | nil =>
    apply Iff.intro
    intro h
    have : List.MinCountBy _ _ _ := h
    cases this
    exact .zero
    intro h
    have : List.MinCountBy _ _ _ := h
    cases this
    exact .zero
  | cons a as ih =>
    rw [erase_cons]
    apply Iff.intro
    · intro g
      split
      · subst a
        replace h := h.resolve_left (fun x => x (mem_cons.mpr (.inl rfl)))
        cases g using MinCountBy.casesCons <;> trivial
      · cases g using MinCountBy.casesCons with
        | head =>
          apply MinCountBy.head
          assumption
          apply (ih _).mp
          assumption
          rcases h with h | h
          left; intro g; apply h (mem_cons.mpr (.inr g))
          right; assumption
        | cons =>
          apply MinCountBy.cons
          apply (ih _).mp
          assumption
          rcases h with h | h
          left; intro g; apply h (mem_cons.mpr (.inr g))
          right; assumption
    · intro g
      split at g
      · subst x
        apply MinCountBy.cons
        assumption
      · cases g using MinCountBy.casesCons with
        | cons _ _ _ g =>
          apply MinCountBy.cons
          apply (ih _).mpr
          assumption
          rcases h with h | h
          left; intro h'; exact h (mem_cons.mpr <| .inr h')
          right; assumption
        | head =>
          apply MinCountBy.head
          assumption
          apply (ih _).mpr
          assumption
          rcases h with h | h
          left; intro h'; exact h (mem_cons.mpr <| .inr h')
          right; assumption

def count_by_elem_erase_if_mem [DecidableEq α] (x: α) (as: Multiset α) (x_in_as: x ∈ as) (px: P x) : as.MinCountBy P n ↔ (as.erase x).MinCountBy P n.pred := by
  cases n with
  | zero =>
    apply Iff.intro
    intro
    exact MinCountBy.zero
    intro
    exact MinCountBy.zero
  | succ n =>
  induction as generalizing n with
  | nil => contradiction
  | cons a as ih =>
    dsimp at ih
    rw [erase_cons]
    split; subst x
    · apply Iff.intro
      intro h
      cases h using MinCountBy.casesCons with
      | cons _ _ _ h =>
        dsimp
        apply h.reduce
        apply Nat.le_succ
      | head => assumption
      intro h
      dsimp at h
      apply MinCountBy.head
      assumption
      assumption
    · dsimp
      apply Iff.intro
      intro h
      cases h using MinCountBy.casesCons
      apply MinCountBy.cons
      apply (ih _ _).mp
      assumption
      cases x_in_as using cases_mem_cons
      contradiction
      assumption
      cases n
      exact .zero
      apply MinCountBy.head
      assumption
      apply (ih _ _).mp
      assumption
      cases x_in_as using cases_mem_cons
      contradiction
      assumption
      intro h
      cases h using MinCountBy.casesCons
      apply MinCountBy.cons
      apply (ih _ _).mpr
      assumption
      cases x_in_as using cases_mem_cons
      contradiction
      assumption
      apply MinCountBy.head
      assumption
      apply (ih _ _).mpr
      assumption
      cases x_in_as using cases_mem_cons
      contradiction
      assumption

def count_elem_erase_if_mem [DecidableEq α] (x: α) (as: Multiset α) (h: x ∈ as) : as.MinCount x n ↔ (as.erase x).MinCount x n.pred := by
  apply count_by_elem_erase_if_mem
  assumption
  rfl

def count_elem_erase [DecidableEq α] (x: α) (as: Multiset α) : as.MinCount x n -> (as.erase x).MinCount x n.pred := by
  intro h
  by_cases mem:x ∈ as
  exact (count_elem_erase_if_mem x _ mem).mp h
  apply ((count_by_erase x _ (.inl mem)).mp h).reduce
  apply Nat.pred_le

def count_erase [DecidableEq α] (x: α) (as: Multiset α) : ∀{y n}, x ≠ y -> (as.MinCount y n ↔ (as.erase x).MinCount y n) := by
  intro y n ne
  apply count_by_erase
  right; assumption

def MinCount.iff_mem {x: α} {as: Multiset α} : as.MinCount x 1 ↔ x ∈ as := by
  induction as with
  | nil =>
    apply Iff.intro
    intro h
    contradiction
    intro h
    contradiction
  | cons a as ih =>
    apply Iff.intro
    intro h
    cases h using MinCount.casesCons
    apply mem_cons.mpr; right
    apply ih.mp
    assumption
    apply mem_cons.mpr; left; rfl
    intro h
    cases h using cases_mem_cons
    apply MinCount.head
    apply MinCount.zero
    apply MinCount.cons
    apply ih.mpr
    assumption

instance : HasSubset (Multiset α) where
  Subset a b := ∀x n, a.MinCount x n -> b.MinCount x n

def sub_trans {a b c: Multiset α}: a ⊆ b -> b ⊆ c -> a ⊆ c := by
   intro ab bc x n y
   apply bc
   apply ab
   assumption

@[refl]
def sub_refl (as: Multiset α): as ⊆ as := fun _ _ => id
def sub_cons {a: α} {as: Multiset α}: as ⊆ a::ₘas := by
  intro x n c
  apply c.cons

def sub_empty {as: Multiset α} : as ⊆ ∅ -> as = ∅ := by
  intro s
  induction as
  rfl
  rename_i a as _
  have := s _ _ (MinCount.head MinCount.zero)
  contradiction

def empty_ne_cons {a: α} {as: Multiset α} : ∅ ≠ a::ₘas := by
  cases as with | mk as =>
  intro h
  have := Quotient.exact h
  have := List.Perm.length_eq this
  contradiction

def mem_spec {as: Multiset α} :
  ∀{x}, x ∈ as ↔ ∃as', as = x::ₘas' := by
  cases as with | mk as =>
  induction as with
  | nil =>
    intro x
    apply Iff.intro
    intro h
    contradiction
    intro ⟨_, h⟩
    have := empty_ne_cons h
    contradiction
  | cons a as ih =>
    intro x
    apply Iff.intro
    intro h
    cases h
    exists ⟦as⟧
    rename_i mem
    have ⟨as', h⟩  := ih.mp mem
    exists a::ₘas'
    show a::ₘ⟦as⟧ = _
    rw [h]
    rw [cons_comm]
    intro ⟨as', h⟩
    cases as' with | mk as' =>
    replace h := Quotient.exact h
    exact (List.Perm.mem_iff h).mpr (.head _)

def sub_mem {x: α} { as bs: Multiset α }:
  as ⊆ bs -> x ∈ as -> x ∈ bs := by
  intro sub mem
  exact MinCount.iff_mem.mp <| sub _ _ (MinCount.iff_mem.mpr mem)

def of_cons_sub_cons {x: α} { as bs: Multiset α }:
  x::ₘas ⊆ x::ₘbs -> as ⊆ bs := by
  -- cases as with | mk as =>
  -- cases bs with | mk bs =>
  intro s
  intro y n cnt
  cases s _ _ cnt.cons using MinCount.casesCons; rename_i cnt'
  assumption
  cases s _ _ cnt.head using MinCount.casesCons; rename_i cnt'
  apply cnt'.reduce
  apply Nat.le_succ
  assumption

def Pairwise.sub {P: α -> α -> Prop} {_: Relation.IsSymmetric P} {as bs: Multiset α} :
  bs ⊆ as ->
  as.Pairwise P -> bs.Pairwise P := by
  intro sub p
  induction bs with
  | nil => apply Pairwise.nil
  | cons b bs ih =>
    apply (ih (sub_trans sub_cons sub)).cons
    intro x mem
    have b_in_as := sub_mem sub (mem_cons.mpr (.inl rfl))
    have ⟨as', eq⟩ := mem_spec.mp b_in_as
    subst as; clear b_in_as
    replace sub := of_cons_sub_cons sub
    apply p.head
    apply sub_mem sub
    assumption

def erase_sub [DecidableEq α] {x₀: α} {as: Multiset α}: as.erase x₀ ⊆ as := by
  intro x n c
  induction as generalizing n with
  | nil => exact c
  | cons a as ih =>
    rw [erase_cons] at c
    split at c
    exact c.cons
    cases c using MinCount.casesCons
    apply MinCount.cons
    apply ih
    assumption
    apply MinCount.head
    apply ih
    assumption

def Pairwise.erase [DecidableEq α] {_: Relation.IsSymmetric P} {x: α} {as: Multiset α} :
  as.Pairwise P -> (as.erase x).Pairwise P := by
  apply Pairwise.sub
  apply erase_sub

-- theorem flatMap_flatMap {m : Multiset α} {n: Multiset β} {f : α → β -> Multiset γ} :
--   m.flatMap (fun a => n.flatMap (fun b => f a b)) = n.flatMap (fun b => m.flatMap (fun a => f a b)) := by
--   quot_ind (m n)
--   induction m generalizing n with
--   | nil =>
--     show ∅ = _
--     symm
--     show flatMap (fun _ => ∅) _ = ∅
--     induction n with
--     | nil => rfl
--     | cons n ns ih =>
--       simp [ih, flatMap_cons, ←mk_cons]
--       rfl
--   | cons m ms ih =>
--     cases n
--     simp [ih, flatMap_cons, ←mk_cons]
--     rfl
--     rw [←mk_cons, flatMap_cons]
--     rw [←mk_cons, flatMap_cons]
--     rw [flatMap_cons]
--     rw [flatMap_cons]
--     simp [append_assoc]
--     congr 1
--     rw [ih]
--     rw [←mk_cons, flatMap_cons]
--     rw [←append_assoc, append_comm (flatMap _ _), append_assoc]
--     congr 1
--     sorry

-- theorem bind_bind (m : Multiset α) (n : Multiset β) {f : α → β → Multiset γ} :
--     ((bind m) fun a => (bind n) fun b => f a b) = (bind n) fun b => (bind m) fun a => f a b :=

end Multiset
