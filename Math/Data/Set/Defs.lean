import Math.Logic.IsEmpty
import Math.Function.Basic
import Math.Order.Defs
import Math.Relation.Defs

section Defs

class SUnion (α: Type*) (β: outParam <| Type*) where
  sUnion : α -> β

class SInter (α: Type*) (β: outParam <| Type*) where
  sInter : α -> β

class SetComplement (α: Type*) where
  scompl : α -> α

prefix:100 "⋃ " => SUnion.sUnion
prefix:100 "⋂ " => SInter.sInter
postfix:max "ᶜ" => SetComplement.scompl

structure Set (α: Type u) where
  Mem : α -> Prop

class SupSet (α: Type*) where
  sSup: Set α -> α

class InfSet (α: Type*) where
  sInf: Set α -> α

def sSup [SupSet α] (s: Set α) : α := SupSet.sSup s
def sInf [InfSet α] (s: Set α) : α := InfSet.sInf s

end Defs

namespace Set

section Basics

instance : Membership α (Set α) where
  mem := Set.Mem

instance : HasSubset (Set α) where
  Subset a b := ∀x ∈ a, x ∈ b

@[simp]
def mk_mem (P: α -> Prop) : ∀{x}, x ∈ mk P ↔ P x := by rfl

@[ext]
def ext (a b : Set α) : (∀x, x ∈ a ↔ x ∈ b) -> a = b := by
  intro h;
  cases a; cases b
  congr; ext; apply h

instance : LE (Set α) where
  le := (· ⊆ ·)
instance : LT (Set α) where
  lt a b :=  a ≤ b ∧ ¬(b ≤ a)
instance : IsLawfulLT (Set α) where

instance : IsPartialOrder (Set α) where
  le_refl _ _ := id
  le_antisymm := by
    intro a b h g
    ext; apply Iff.intro
    apply h
    apply g
  le_trans h g x hx := g _ (h x hx)

instance : @Relation.IsPartialOrder (Set α) (· ⊆ ·) (· = ·) where
  trans := le_trans (α := Set α)
  refl := le_refl (α := Set α)
  antisymm_by := le_antisymm (α := Set α)

def empty (α: Type*) : Set α where
  Mem _ := False

instance : EmptyCollection (Set α) where
  emptyCollection := empty α
instance : Bot (Set α) where
  bot := empty α

@[simp] def not_mem_empty (x: α) : ¬x ∈ (∅: Set α) := nofun
@[simp] def not_mem_bot (x: α) : ¬x ∈ (⊥: Set α) := nofun

def univ (α: Type*) : Set α where
  Mem _ := True

instance : Top (Set α) where
  top := univ α

@[simp] def mem_univ (x: α) : x ∈ (⊤: Set α) := True.intro

instance : Union (Set α) where
  union a b := { Mem x := x ∈ a ∨ x ∈ b }
instance : Max (Set α) where
  max a b := a ∪ b

@[simp] def mem_union {a b: Set α} : ∀{x}, x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b := Iff.rfl
@[simp] def mem_max {a b: Set α} : ∀{x}, x ∈ a ⊔ b ↔ x ∈ a ∨ x ∈ b := Iff.rfl

instance : Inter (Set α) where
  inter a b := { Mem x := x ∈ a ∧ x ∈ b }
instance : Min (Set α) where
  min a b := a ∩ b

@[simp] def mem_inter {a b: Set α} : ∀{x}, x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b := Iff.rfl
@[simp] def mem_min {a b: Set α} : ∀{x}, x ∈ a ⊓ b ↔ x ∈ a ∧ x ∈ b := Iff.rfl

instance : IsLattice (Set α) where
  le_max_left := by
    intro a b x
    simp
    apply Or.inl
  le_max_right := by
    intro a b x
    simp
    apply Or.inr
  max_le := by
    intro S a b h g x
    simp
    intro h; cases h
    apply h
    assumption
    apply g
    assumption
  min_le_left := by
    intro a b x
    simp
    intros; assumption
  min_le_right := by
    intro a b x
    simp
  le_min := by
    intro a b S h g x
    simp
    intro
    apply And.intro
    apply h
    assumption
    apply g
    assumption

instance : IsLawfulTop (Set α) where
  le_top _ _ _ := True.intro

instance : IsLawfulBot (Set α) where
  bot_le _ _ := False.elim

def image (f: α -> β) (s: Set α) : Set β where
  Mem b := ∃a ∈ s, b = f a

@[simp] def mem_image {f: α -> β} {s: Set α} : ∀{x}, x ∈ s.image f ↔ ∃a ∈ s, x = f a := Iff.rfl

def range (f: α -> β) : Set β where
  Mem b := ∃a, b = f a

@[simp] def mem_range {f: α -> β} : ∀{x}, x ∈ range f ↔ ∃a, x = f a := Iff.rfl

def preimage (f: α -> β) (s: Set β) : Set α where
  Mem a := f a ∈ s

@[simp] def mem_preimage {f: α -> β} {s: Set β} : ∀{x}, x ∈ s.preimage f ↔ f x ∈ s := Iff.rfl

instance : SetComplement (Set α) where
  scompl s := { Mem x := x ∉ s }

@[simp] def mem_scompl {s: Set α} : ∀{x}, x ∈ sᶜ ↔ x ∉ s := Iff.rfl

instance : SDiff (Set α) where
  sdiff a b := a ∩ bᶜ

@[simp] def mem_sdiff {a b: Set α} : ∀{x}, x ∈ a \ b ↔ x ∈ a ∧ x ∉ b := Iff.rfl

instance : Singleton α (Set α) where
  singleton a := { Mem := (· = a) }

@[simp] def mem_singleton {a: α} : ∀{x}, x ∈ ({a}: Set α) ↔ x = a := Iff.rfl

instance : Insert α (Set α) where
  insert a s := {a} ∪ s

@[simp] def mem_insert {a: α} {s: Set α} : ∀{x}, x ∈ insert a s ↔ x = a ∨ x ∈ s := Iff.rfl

def support [Zero β] (f: α -> β) : Set α := (Set.preimage f {0})ᶜ

@[simp] def mem_support [Zero β] {f: α -> β} : ∀{x}, x ∈ support f ↔ f x ≠ 0 := Iff.rfl

def sum (a: Set α) (b: Set β) : Set (α ⊕ β) where
  Mem
  | .inl x => x ∈ a
  | .inr x => x ∈ b

@[simp] def mem_sum_inl {a: Set α} {b: Set β} : ∀{x}, Sum.inl x ∈ a.sum b ↔ x ∈ a := Iff.rfl
@[simp] def mem_sum_inr {a: Set α} {b: Set β} : ∀{x}, Sum.inr x ∈ a.sum b ↔ x ∈ b := Iff.rfl

def prod (a: Set α) (b: Set β) : Set (α × β) where
  Mem x := x.1 ∈ a ∧ x.2 ∈ b

@[simp] def mem_prod {a: Set α} {b: Set β} : ∀{x}, x ∈ a.prod b ↔ x.1 ∈ a ∧ x.2 ∈ b := Iff.rfl

def pi {ι: Type*} {α: ι -> Type*} (a: ∀x, Set (α x)) : Set (∀x, α x) where
  Mem x := ∀i: ι, x i ∈ a i

@[simp] def mem_pi {ι: Type*} {α: ι -> Type*} {a: ∀x, Set (α x)}: ∀{x}, x ∈ pi a ↔ ∀i, x i ∈ a i := Iff.rfl

def powerset (s: Set α) : Set (Set α) where
  Mem x := x ⊆ s

@[simp] def mem_powerset {s: Set α} : ∀{x}, x ∈ s.powerset ↔ x ⊆ s := Iff.rfl

@[simp] def mem_pair {a b: α} : ∀{x}, x ∈ ({a, b}: Set α) ↔ x = a ∨ x = b := Iff.rfl

@[coe]
def ofList (l: List α) : Set α where
  Mem x := x ∈ l

instance : Coe (List α) (Set α) := ⟨ofList⟩

@[simp] def mem_ofList {l : List α} : ∀{x}, x ∈ (l: Set α) ↔ x ∈ l := Iff.rfl

def IsFinite (s: Set α) : Prop := ∃l: List α, s = l

end Basics

end Set

section iOps

class IsLawfulSupSet (α: Type*) [LE α] [SupSet α] where
  le_sSup: ∀{s: Set α} {x: α}, x ∈ s -> x ≤ sSup s
class IsLawfulInfSet (α: Type*) [LE α] [InfSet α] where
  sInf_le: ∀{s: Set α} {x: α}, x ∈ s -> sInf s ≤ x

def le_sSup [LE α] [SupSet α] [IsLawfulSupSet α]: ∀{s: Set α} {x: α}, x ∈ s -> x ≤ sSup s :=
  IsLawfulSupSet.le_sSup

def sInf_le [LE α] [InfSet α] [IsLawfulInfSet α]: ∀{s: Set α} {x: α}, x ∈ s -> sInf s ≤ x :=
  IsLawfulInfSet.sInf_le

def iSup [SupSet α] (s: ι -> α) : α := sSup (Set.range s)
def iInf [InfSet α] (s: ι -> α) : α := sInf (Set.range s)

section Syntax

open Lean Meta PrettyPrinter TSyntax.Compat

notation "⨆ " xs:60 => sSup xs
notation "⨅ " xs:60 => sInf xs

macro (name := big_op_iSup) "⨆ " xs:explicitBinders ", " b:term:60 : term => expandExplicitBinders ``iSup xs b
macro (name := big_op_iInf) "⨅ " xs:explicitBinders ", " b:term:60 : term => expandExplicitBinders ``iInf xs b

@[app_unexpander iSup] def unexpand_iSup : Unexpander
  | `($(_) fun $x:ident => ⨆ $xs:binderIdent*, $b) => `(⨆ $x:ident $xs:binderIdent*, $b)
  | `($(_) fun $x:ident => $b)                     => `(⨆ $x:ident, $b)
  | `($(_) fun ($x:ident : $t) => $b)              => `(⨆ ($x:ident : $t), $b)
  | _                                              => throw ()

@[app_unexpander iInf] def unexpand_iInf : Unexpander
  | `($(_) fun $x:ident => ⨅ $xs:binderIdent*, $b) => `(⨅ $x:ident $xs:binderIdent*, $b)
  | `($(_) fun $x:ident => $b)                     => `(⨅ $x:ident, $b)
  | `($(_) fun ($x:ident : $t) => $b)              => `(⨅ ($x:ident : $t), $b)
  | _                                              => throw ()

end Syntax

end iOps

namespace Set

section SetOps

instance : SupSet (Set α) where
  sSup U := { Mem x := ∃u ∈ U, x ∈ u }

instance : InfSet (Set α) where
  sInf U := { Mem x := ∀u ∈ U, x ∈ u }

instance : SUnion (Set (Set α)) (Set α) where
  sUnion U := ⨆U

instance : SInter (Set (Set α)) (Set α) where
  sInter U := ⨅U

@[simp] def mem_sUnion {S: Set (Set α)} : ∀{x}, x ∈ ⋃ S ↔ ∃s ∈ S, x ∈ s := Iff.rfl
@[simp] def mem_sInter {S: Set (Set α)} : ∀{x}, x ∈ ⋂ S ↔ ∀s ∈ S, x ∈ s := Iff.rfl

@[simp] def sSup_eq_sUnion (S: Set (Set α)) : ⨆ S = ⋃ S := rfl
@[simp] def sInf_eq_sInter (S: Set (Set α)) : ⨅ S = ⋂ S := rfl

@[simp] def mem_iSup {f: ι -> Set α} : ∀{x}, x ∈ (⨆i, f i) ↔ ∃i, x ∈ f i := by
  simp [iSup]
  intro x
  apply Iff.intro
  simp
  intro i hi
  exists i
  rintro ⟨i, h⟩
  exists f i
  apply And.intro _ h
  exists i
@[simp] def mem_iInf {f: ι -> Set α} : ∀{x}, x ∈ (⨅i, f i) ↔ ∀i, x ∈ f i := by simp [iInf]

instance : IsLawfulSupSet (Set α) where
  le_sSup := by
    intro s x h y hy
    exists x

instance : IsLawfulInfSet (Set α) where
  sInf_le := by
    intro s x h y hy
    apply hy
    assumption

end SetOps

section «Type»

@[coe]
abbrev «Type» (s: Set α) := { x // x ∈ s }

instance : CoeSort (Set α) (Type _) where
  coe s := s.Type

def attach (s: Set α) : Set s := ⊤

@[simp] def mem_attach (s: Set α) : ∀x, x ∈ s.attach := mem_univ

end «Type»

section Monad

@[irreducible]
def bind (a: Set α) (f: α -> Set β) : Set β := iSup fun x: a => f x

unseal bind in
@[simp] def mem_bind {A: Set α} {f: α -> Set β} : ∀{x}, x ∈ bind A f ↔  ∃a ∈ A, x ∈ f a := by
  simp [bind]

instance : Monad Set where
  pure a := {a}
  bind := bind
  map := image

@[simp] def bind_eq_bind : Bind.bind = bind (α := α) (β := β) := rfl
@[simp] def map_eq_image : Functor.map = (image (α := α) (β := β)) := rfl
@[simp] def pure_eq_singleton (x: α) : pure x = ({x}: Set α) := rfl

@[simp] def bind_singleton (a: α) (f: α -> Set β) : bind {a} f = f a := by ext; simp

instance : LawfulMonad Set where
  map_const := by simp [Functor.mapConst]
  id_map := by intro α s; ext; simp
  seqLeft_eq := by
    intro α β x y; ext z; simp [SeqLeft.seqLeft, Seq.seq]
    apply Iff.intro
    · intro ⟨_, b, _⟩
      exists Function.const _ z
      apply And.intro
      exists z
      exists b
    · intro ⟨_, ⟨_, h, rfl⟩, ⟨b, g, rfl⟩⟩
      apply And.intro h
      exists b
  seqRight_eq := by
    intro α β x y; ext z; simp [SeqRight.seqRight, Seq.seq]
    apply Iff.intro
    · intro ⟨⟨a, _⟩, _⟩
      exists id
      apply And.intro (And.intro _ rfl) _
      exists a
      exists z
    · rintro ⟨_, ⟨⟨a, _⟩, rfl⟩, ⟨b, h, rfl⟩⟩
      apply And.intro
      exists a
      assumption
  pure_seq  := by
    intro α β g x
    simp [Seq.seq]
  bind_pure_comp := by
    intro α β f x
    ext b
    simp
  bind_map := by
    intro α β f x
    simp [Seq.seq]
  pure_bind := by simp
  bind_assoc := by
    intro α β γ s f g
    ext x;
    simp
    apply Iff.intro
    · intro ⟨b, ⟨a, _, _⟩, _⟩
      exists a
      apply And.intro
      assumption
      exists b
    · intro ⟨a, _, b, _, _⟩
      exists b
      apply And.intro
      exists a
      assumption

end Monad

section Nonempty

protected abbrev Nonempty (s: Set α) := Nonempty s

def nonempty_iff_exists {s: Set α} : s.Nonempty ↔ ∃x, x ∈ s := by
  apply Iff.intro
  intro ⟨x, sh⟩
  exists x
  intro ⟨x, sh⟩
  exists x

def exists_elem (s: Set α) [s.Nonempty] : ∃x, x ∈ s := by
  rwa [←nonempty_iff_exists]

instance (a: α) : Set.Nonempty {a} := by exists a

instance (a: α) (s: Set α) : Set.Nonempty (insert a s) := by exists a; simp

instance (a b: Set α) [a.Nonempty] : (a ∪ b).Nonempty := by
  have ⟨x, h⟩ := exists_elem a
  exists x
  simp [h]

instance (a b: Set α) [b.Nonempty] : (a ∪ b).Nonempty := by
  have ⟨x, h⟩ := exists_elem b
  exists x
  simp [h]

def nonempty_of_inter_left (a b: Set α) [(a ∩ b).Nonempty] : a.Nonempty := by
  have ⟨x, _, _⟩ := exists_elem (a ∩ b)
  exists x

def nonempty_of_inter_right (a b: Set α) [(a ∩ b).Nonempty] : b.Nonempty := by
  have ⟨x, _, _⟩ := exists_elem (a ∩ b)
  exists x

def nonempty_attach {s: Set α} : s.attach.Nonempty ↔ s.Nonempty := by simp [nonempty_iff_exists]

@[simp]
def not_nonempty {a: Set α} : ¬a.Nonempty ↔ a = ∅ := by
  apply Iff.intro
  intro h; ext x; simp
  intro g; apply h; exists x
  rintro rfl
  intro h
  obtain ⟨x, hx⟩ := h
  contradiction
@[simp]
def ne_empty {a: Set α} : a ≠ ∅ ↔ a.Nonempty := by
  apply Classical.not_iff_not.mpr
  simp

@[simp]
def is_empty (s: Set α) : IsEmpty s ↔ s = ∅ := by
  rw [←not_nonempty]
  apply Iff.intro
  intro h ⟨g⟩
  exact elim_empty g
  intro h
  exact { elim s := h ⟨s⟩ }

def empty_not_nonempty : ¬Set.Nonempty (∅: Set α) := nofun

macro_rules
| `(tactic|contradiction) => `(tactic|exfalso; apply empty_not_nonempty; assumption)

instance : IsEmpty (∅: Set α) where
  elim x := x.property

end Nonempty

section MinElem

variable (r: α -> α -> Prop) [Relation.IsWellFounded r]
variable {s: Set α} (h: s.Nonempty)

private def exists_min_elem : ∃x ∈ s, ∀y ∈ s, ¬r y x := by
  have ⟨x, hx, h⟩ := Relation.exists_min r (nonempty_iff_exists.mp h)
  refine ⟨x, hx, ?_⟩
  intro y hy g ; apply h
  assumption
  assumption

noncomputable def min : α := Classical.choose (exists_min_elem r h)
noncomputable def min_mem : min r h ∈ s := (Classical.choose_spec (exists_min_elem r h)).left
noncomputable def not_lt_min : ∀y ∈ s, ¬r y (min r h) := (Classical.choose_spec (exists_min_elem r h)).right

attribute [irreducible] min

end MinElem

section BasicTheorems

@[refl, simp]
def sub_refl (a: Set α) : a ⊆ a := Relation.refl _
def sub_trans {a b c: Set α} : a ⊆ b -> b ⊆ c -> a ⊆ c := trans
def sub_antisymm {a b: Set α} : a ⊆ b -> b ⊆ a -> a = b := antisymm _

def union_comm (a b: Set α) : a ∪ b = b ∪ a := max_comm _ _
def inter_comm (a b: Set α) : a ∩ b = b ∩ a := min_comm _ _
def union_assoc (a b c: Set α) : a ∪ b ∪ c = a ∪ (b ∪ c) := max_assoc _ _ _
def inter_assoc (a b c: Set α) : a ∩ b ∩ c = a ∩ (b ∩ c) := min_assoc _ _ _

def sub_union_left (a b: Set α) : a ⊆ a ∪ b := le_max_left a b
def sub_union_right (a b: Set α) : b ⊆ a ∪ b := le_max_right a b
def inter_sub_left (a b: Set α) : a ∩ b ⊆ a := min_le_left a b
def inter_sub_right (a b: Set α) : a ∩ b ⊆ b := min_le_right a b

def sub_insert (a: α) (s: Set α) : s ⊆ insert a s := sub_union_right _ _

def sub_sUnion {S: Set (Set α)} {s: Set α} : s ∈ S -> s ⊆ ⋃ S := le_sSup
def sInter_sub {S: Set (Set α)} {s: Set α} : s ∈ S -> ⋂ S ⊆ s := sInf_le

@[simp] def sub_univ (s: Set α) : s ⊆ ⊤ := le_top (α := Set α) _
@[simp] def univ_sub {s: Set α} : ⊤ ⊆ s ↔ s = ⊤ := top_le (α := Set α)

@[simp] def empty_sub (s: Set α) : ∅ ⊆ s := bot_le (α := Set α) _
@[simp] def sub_empty {s: Set α} : s ⊆ ∅ ↔ s = ∅ := le_bot (α := Set α)

def mem_image' {a: Set α} {f: α -> β} (h: x ∈ a) : f x ∈ a.image f := by
  apply mem_image.mpr
  exists x

def mem_range' {f: α -> β} : f x ∈ range f := by
  simp
  exists x

def range_comp {f: α -> β} {g: β -> γ} :
  x ∈ Set.range f ->
  g x ∈ Set.range (g ∘ f) := by
  intro mem
  apply Set.mem_range.mpr
  obtain ⟨a', eq⟩  := Set.mem_range.mp mem
  exact ⟨a', eq ▸ rfl⟩

@[simp] def preimage_id (s: Set α) : s.preimage id = s := rfl
def preimage_preimage (s: Set α) (f: γ -> β) (g: β -> α) : (s.preimage g).preimage f = s.preimage (g ∘ f) := by
  rfl

@[simp] def sdiff_self (s: Set α) : s \ s = ∅ := by ext; simp
@[simp] def union_self (s: Set α) : s ∪ s = s := by ext; simp
@[simp] def inter_self (s: Set α) : s ∩ s = s := by ext; simp

instance : Subsingleton (∅: Set α) where
  allEq := nofun
instance (a: α) : Subsingleton ({a}: Set α) where
  allEq a b := by ext; rw [a.property, b.property]
instance (U: Set (Set α)) [U.Nonempty] [∀u: U, Subsingleton u] : Subsingleton (⋂ U) where
  allEq := by
    intro ⟨a, ha⟩ ⟨b, hb⟩
    ext
    simp
    have ⟨u, hu⟩ := exists_elem U
    replace ha := ha u hu
    replace hb := hb u hu
    let a' : u := ⟨a, ha⟩
    let b' : u := ⟨b, hb⟩
    show a'.val = b'.val
    congr
    rename_i h
    apply (h ⟨u, hu⟩).allEq
instance (a b: Set α) [Subsingleton a] : Subsingleton (a ∩ b: Set _) where
  allEq := by
    intro ⟨x, hx⟩ ⟨y, hy⟩
    let a' : a := ⟨x, hx.left⟩
    let b' : a := ⟨y, hy.left⟩
    congr
    show a'.val = b'.val
    congr
    rename_i h
    apply Subsingleton.allEq
instance (a b: Set α) [Subsingleton b] : Subsingleton (a ∩ b: Set _) where
  allEq := by
    intro ⟨x, hx⟩ ⟨y, hy⟩
    let a' : b := ⟨x, hx.right⟩
    let b' : b := ⟨y, hy.right⟩
    congr
    show a'.val = b'.val
    congr
    rename_i h
    apply Subsingleton.allEq

end BasicTheorems

section Empty

@[simp] def union_empty (s: Set α) : s ∪ ∅ = s := by ext; simp
@[simp] def empty_union (s: Set α) : ∅ ∪ s = s := by ext; simp
@[simp] def inter_empty (s: Set α) : s ∩ ∅ = ∅ := by ext; simp
@[simp] def empty_inter (s: Set α) : ∅ ∩ s = ∅ := by ext; simp
@[simp] def sUnion_empty : ⋃(∅: Set (Set α)) = ∅ := by ext; simp
@[simp] def sInter_empty : ⋂(∅: Set (Set α)) = ⊤ := by ext; simp
@[simp] def sdiff_empty (s: Set α) : s \ ∅ = s := by ext; simp
@[simp] def empty_sdiff (s: Set α) : ∅ \ s = ∅ := by ext; simp
@[simp] def powerset_empty : powerset (∅: Set α) = {∅} := by ext; simp
@[simp] def preimage_empty (f: α -> β) : preimage f ∅ = ∅ := rfl
@[simp] def image_empty (f: α -> β) : image f ∅ = ∅ := by ext; simp
@[simp] def compl_empty : (∅: Set α)ᶜ = ⊤ := by ext; simp
@[simp] def insert_empty (x: α) : insert x ∅ = ({x}: Set α) := by ext; simp
@[simp] def attach_empty : attach (∅: Set α) = ∅ := by ext x; exact elim_empty x
@[simp] def bind_empty (f: α -> Set β) : bind ∅ f = ∅ := by ext; simp

end Empty

section Univ

@[simp] def union_univ (s: Set α) : s ∪ ⊤ = ⊤ := by ext; simp
@[simp] def univ_union (s: Set α) : ⊤ ∪ s = ⊤ := by ext; simp
@[simp] def inter_univ (s: Set α) : s ∩ ⊤ = s := by ext; simp
@[simp] def univ_inter (s: Set α) : ⊤ ∩ s = s := by ext; simp
@[simp] def sUnion_univ : ⋃(⊤: Set (Set α)) = ⊤ := by
  ext
  simp
  rename_i x
  exists {x}
@[simp] def sInter_univ : ⋂(⊤: Set (Set α)) = ∅ := by
  ext
  simp
  exists ∅
  simp
@[simp] def sdiff_univ (s: Set α) : s \ ⊤ = ∅ := by ext; simp
@[simp] def univ_sdiff (s: Set α) : ⊤ \ s = sᶜ := by ext; simp
@[simp] def powerset_univ : powerset (⊤: Set α) = ⊤ := by ext; simp
@[simp] def preimage_univ (f: α -> β) : preimage f ⊤ = ⊤ := rfl
@[simp] def image_univ (f: α -> β) : image f ⊤ = range f := by ext; simp
@[simp] def compl_univ : (⊤: Set α)ᶜ = ∅ := by ext; simp
@[simp] def insert_univ (x: α) : insert x ⊤ = (⊤: Set α) := by ext; simp

end Univ

section Insert

variable (x: α) (a b: Set α)

@[simp] def union_insert : a ∪ (insert x b) = insert x (a ∪ b) := by ext x; simp; ac_nf
@[simp] def insert_union : (insert x a) ∪ b = insert x (a ∪ b) := by ext x; simp; ac_nf
@[simp] def insert_inter_insert : (insert x a) ∩ (insert x b) = insert x (a ∩ b) := by ext; simp [←or_and_left]
@[simp] def sUnion_insert (s: Set α) (U: Set (Set α)) : ⋃(insert s U) = s ∪ ⋃U := by ext; simp
@[simp] def sUnion_singleton (s: Set α) : ⋃({s}: Set (Set _)) = s := by ext; simp
@[simp] def sUnion_pair : ⋃({a, b}: Set (Set _)) = a ∪ b := by simp
@[simp] def sInter_insert (s: Set α) (U: Set (Set α)) : ⋂(insert s U) = s ∩ ⋂U := by ext; simp
@[simp] def sInter_singleton (s: Set α) : ⋂({s}: Set (Set _)) = s := by ext; simp
@[simp] def sInter_pair : ⋂({a, b}: Set (Set _)) = a ∩ b := by simp
@[simp] def image_insert (f: α -> β) : image f (insert x a) = insert (f x) (image f a) := by ext; simp
@[simp] def image_singleton (f: α -> β) : image f {x} = {f x} := by ext; simp
@[simp] def bind_insert (f: α -> Set β) : bind (insert x a) f = f x ∪ bind a f := by ext; simp

end Insert

section Theorems

def image_const_of_nonempty (a: Set α) (b: β) : a.Nonempty -> a.image (fun _ => b) = {b} := by
  intro ⟨a', ha'⟩
  ext x
  simp [mem_image, mem_singleton]
  intro h
  exists a'

def ofList_empty : ofList [] = (∅: Set α) := by ext; simp
def ofList_cons (a: α) (as: List α) : ofList (a::as) = insert a (as: Set α) := by ext; simp
def ofList_append (as bs: List α) : ofList (as ++ bs) = (as: Set α) ∪ (bs: Set α) := by ext; simp

def image_id (s: Set α) : s.image id = s := by ext; simp
def image_id' (s: Set α) {f: α -> α} (h: ∀x, f x = x) : s.image f = s := by
  rw [show f = id from ?_, image_id]
  ext; apply h

def preimage_sUnion (s: Set (Set α)) (f: β -> α) : (⋃s).preimage f = ⋃(s.image fun x => x.preimage f) := by
  ext x
  apply Iff.intro
  intro ⟨s', s'_in_s, fx_in_s'⟩
  exists s'.preimage f
  apply And.intro _ fx_in_s'
  apply Set.mem_image'
  assumption
  intro ⟨_, ⟨s', s'_in, eq⟩ , x_in_s'⟩
  subst eq
  dsimp at x_in_s'
  exists s'

@[simp] def image_image (s: Set α) (f: α -> β) (g: β -> γ) : (s.image f).image g = s.image (g ∘ f) := by
  ext x
  apply Iff.intro
  intro ⟨s', ⟨_, s'_in_s, eq⟩ , fx_in_s'⟩
  subst x; subst eq
  apply Set.mem_image'
  assumption
  intro ⟨_, _, eq⟩
  subst eq
  apply Set.mem_image'
  apply Set.mem_image'
  assumption

def sub_image_preimage (s: Set α) (f: α -> β) : s ⊆ (s.image f).preimage f := by
  intro x mem
  exists x

def image_preimage' (s: Set α) (f: α -> β) (h: ∀a b, f a = f b -> a ∈ s -> b ∈ s) : (s.image f).preimage f = s := by
  ext x
  rw [mem_preimage, mem_image]
  apply Iff.intro
  intro ⟨y, mem, eq⟩
  apply h
  symm; assumption
  assumption
  intro mem
  exists x

def image_preimage (s: Set α) (f: α -> β) (hf: Function.Injective f) : (s.image f).preimage f = s := by
  apply image_preimage'
  intro a b h g
  rw [hf.eq_iff] at h
  rwa [←h]

@[simp] def image_union (a b: Set α) (f: α -> β) : (a ∪ b).image f = a.image f ∪ b.image f := by
  ext x
  simp [mem_union, mem_image]
  apply Iff.intro
  rintro ⟨x, hx, rfl⟩
  cases hx
  left; exists x
  right; exists x
  intro h; rcases h with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
  exists x; apply And.intro _ rfl; left; assumption
  exists x; apply And.intro _ rfl; right; assumption

def image_inter' (A B: Set α) (f: α -> β) : (A ∩ B).image f ⊆ A.image f ∩ B.image f := by
  intro b
  intro ⟨a, ⟨a_in_A, a_in_B⟩, eq⟩
  subst b
  apply And.intro
  exists a
  exists a

def image_inter (A B: Set α) (f: α -> β) (h: Function.Injective f) : (A ∩ B).image f = A.image f ∩ B.image f := by
  ext b
  simp [Set.mem_image, Set.mem_inter]
  apply Iff.intro
  apply image_inter'
  intro ⟨⟨a₀, a₀_in_A, eq₀⟩ , ⟨a₁, a₁_in_B, eq₁⟩⟩
  subst eq₀
  cases h eq₁
  exists a₀

def preimage_inter (A B: Set β) (f: α -> β) : (A ∩ B).preimage f = A.preimage f ∩ B.preimage f := rfl

def attach_image_val (s: Set α) : s.attach.image Subtype.val = s := by
  ext x
  apply Iff.intro
  intro ⟨y, _, _⟩
  subst x
  exact y.property
  intro mem
  exists ⟨x, mem⟩

def mem_image_of_inj (a: Set α) (f: α -> β) (h: Function.Injective f) : f x ∈ a.image f ↔ x ∈ a := by
  apply Iff.intro
  intro ⟨_, _, g⟩
  cases h g
  assumption
  apply mem_image'

def sum_eq_image_union (a: Set α) (b: Set β) : a.sum b = a.image .inl ∪ b.image .inr := by
  ext x; cases x <;> simp

@[simp] def sum_preimage_inl (a: Set α) (b: Set β) : (a.sum b).preimage .inl = a := by
  ext x; simp
@[simp] def sum_preimage_inr (a: Set α) (b: Set β) : (a.sum b).preimage .inr = b := by
  ext x; simp

def sum_spec (a: Set α) (b: Set β) : a.sum b = ⋂ (Set.mk fun s: Set (α ⊕ β) => a ⊆ s.preimage .inl ∧ b ⊆ s.preimage .inr) := by
  ext x
  simp
  rcases x with x | x
  · simp
    apply Iff.intro
    intro h s ha hb
    apply ha
    assumption
    intro h
    apply h (a.sum b)
    simp
    simp
  · simp
    apply Iff.intro
    intro h s ha hb
    apply hb
    assumption
    intro h
    apply h (a.sum b)
    simp
    simp

end Theorems

end Set
