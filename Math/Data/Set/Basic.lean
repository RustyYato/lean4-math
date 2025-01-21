import Math.Type.Basic
import Math.Function.Basic
import Math.Order.Dual
import Math.Relation.Basic

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

namespace Set

instance {α} : Membership α (Set α) := ⟨Set.Mem⟩
instance {α} : HasSubset (Set α) where
  Subset a b := ∀x ∈ a, x ∈ b
instance {α} : HasSSubset (Set α) where
  SSubset a b := a ≠ b ∧ a ⊆ b

def univ α : Set α := .mk fun _ => True
def empty α : Set α := .mk fun _ => False

instance : EmptyCollection (Set α) where
  emptyCollection := empty α

instance : Nonempty (Set α) := ⟨∅⟩

def mem_univ : ∀x, x ∈ Set.univ α := fun _ => True.intro
def not_mem_empty : ∀{x}, ¬x ∈ Set.empty α := False.elim

@[ext]
def ext (a b: Set α) : (∀x: α, x ∈ a ↔ x ∈ b) -> a = b := by
  intro h
  cases a; cases b
  congr
  funext x
  apply propext
  apply h
def ext_empty (a: Set α) : (∀x: α, ¬x ∈ a) -> a = ∅ := by
  intro h
  ext x
  simp [h]
  apply not_mem_empty
def ext_univ (a: Set α) : (∀x: α, x ∈ a) -> a = univ _ := by
  intro h
  ext x
  simp [h]
  apply mem_univ

def univ_eq_empty_of_isempty [IsEmpty α] : Set.univ α = Set.empty α := by
  ext x
  exact (IsEmpty.elim x).elim

@[refl, simp]
def sub_refl (a: Set α) : a ⊆ a := fun _ => id
def sub_trans {a b c: Set α} (x: a ⊆ b) (y: b ⊆ c) : a ⊆ c := by
  intro z h
  apply y
  apply x
  assumption

def sub_antisymm {a b: Set α} : a ⊆ b -> b ⊆ a -> a = b := by
  intro ab ba
  ext x
  apply Iff.intro
  apply ab
  apply ba

def union (a b: Set α) : Set α := mk fun x => x ∈ a ∨ x ∈ b
instance : Union (Set α) := ⟨.union⟩
def mem_union {a b: Set α} : ∀{x}, x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b := Iff.refl _

def inter (a b: Set α) : Set α := mk fun x => x ∈ a ∧ x ∈ b
instance : Inter (Set α) := ⟨.inter⟩
def mem_inter {a b: Set α} : ∀{x}, x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b := Iff.refl _

def sep (P: α -> Prop) (a: Set α) : Set α := mk fun x => x ∈ a ∧ P x
def mem_sep {P: α -> Prop} {a: Set α} : ∀{x}, x ∈ a.sep P ↔ x ∈ a ∧ P x := Iff.refl _

def sUnion (a: Set (Set α)) : Set α := .mk fun x => ∃a' ∈ a, x ∈ a'
instance : SUnion (Set (Set α)) (Set α) := ⟨(·.sUnion)⟩
def mem_sUnion {a: Set (Set α)} : ∀{x}, x ∈ ⋃ a ↔ ∃a' ∈ a, x ∈ a' := Iff.refl _

def sInter (a: Set (Set α)) : Set α := .mk fun x => ∀a' ∈ a, x ∈ a'
instance : SInter (Set (Set α)) (Set α) := ⟨(·.sInter)⟩
def mem_sInter {a: Set (Set α)} : ∀{x}, x ∈ ⋂ a ↔ ∀a' ∈ a, x ∈ a' := Iff.refl _

@[simp]
def sUnion_empty : ⋃(∅: Set (Set α)) = ∅ := by
  apply ext_empty
  intro x
  rw [mem_sUnion]
  intro ⟨_, _, _⟩
  contradiction

@[simp]
def sInter_empty : ⋂(∅: Set (Set α)) = univ _ := by
  apply ext_univ
  intro x
  rw [mem_sInter]
  intros
  contradiction

def sub_sUnion (a: Set α) (s: Set (Set α)): a ∈ s -> a ⊆ ⋃s := by
  intro mem x x_in_a
  rw [mem_sUnion]
  exists a

def sInter_sub (a: Set α) (s: Set (Set α)): a ∈ s -> ⋂s ⊆ a := by
  intro mem x
  rw [mem_sInter]
  intro h
  apply h
  assumption

def preimage (a: Set α) (f: β -> α) : Set β := mk fun x => f x ∈ a
def mem_preimage {a: Set α} {f: β -> α} : ∀{x}, x ∈ a.preimage f ↔ f x ∈ a := Iff.refl _
def image (a: Set α) (f: α -> β) : Set β := mk fun x => ∃a' ∈ a, x = f a'
def mem_image {a: Set α} {f: α -> β} : ∀{x}, x ∈ a.image f ↔ ∃a' ∈ a, x = f a' := Iff.refl _
def mem_image' {a: Set α} {f: α -> β} (h: x ∈ a) : f x ∈ a.image f := by
  apply mem_image.mpr
  exists x
def range (f: α -> β) : Set β := mk fun x => ∃a', x = f a'
def mem_range {f: α -> β} : ∀{x}, x ∈ range f ↔ ∃a', x = f a' := Iff.rfl

def powerset (a: Set α) : Set (Set α) := mk fun x => x ⊆ a
def mem_powerset {a: Set α} : ∀{x}, x ∈ a.powerset ↔ x ⊆ a := Iff.refl _

def compl (a: Set α) : Set α := mk fun x => x ∉ a
instance : SetComplement (Set α) where
  scompl := compl
def mem_compl {a: Set α} : ∀{x}, x ∈ aᶜ ↔ x ∉ a := Iff.refl _

def univ_compl : (Set.univ α)ᶜ = ∅ := by
  apply ext_empty
  intro x h
  exact h True.intro

def empty_compl : ∅ᶜ = Set.univ α := by
  apply ext_univ
  intro x h
  contradiction

def Nonempty (a: Set α) := ∃x, x ∈ a
abbrev Elem (a: Set α) := { x // x ∈ a }

instance {α: Type u} : CoeSort (Set α) (Type u) := ⟨Set.Elem⟩

instance : Singleton α (Set α) where
  singleton a := mk fun x => x = a
def mem_singleton {a: α}: ∀{x}, x ∈ ({a}: Set α) ↔ x = a := Iff.refl _

instance : Insert α (Set α) where
  insert a x := {a} ∪ x
def mem_insert {a: α} {as: Set α}: ∀{x}, x ∈ Insert.insert a as ↔ x = a ∨ x ∈ as := Iff.refl _

end Set

class SupSet (α: Type*) where
  sSup: Set α -> α

class InfSet (α: Type*) where
  sInf: Set α -> α

export SupSet (sSup)
export InfSet (sInf)

instance [InfSet α] : SupSet (OrderDual α) where
  sSup := sInf (α := α)
instance [SupSet α] : InfSet (OrderDual α) where
  sInf := sSup (α := α)

def iSup [SupSet α] (s: ι -> α) : α := sSup (Set.range s)
def iInf [InfSet α] (s: ι -> α) : α := sInf (Set.range s)

instance : SupSet (Set α) where
  sSup x := ⋃x
instance : InfSet (Set α) where
  sInf x := ⋂x

namespace Set

def sub_sSup (a: Set α) (s: Set (Set α)): a ∈ s -> a ⊆ sSup s := sub_sUnion _ _
def sInf_sub (a: Set α) (s: Set (Set α)): a ∈ s -> sInf s ⊆ a := sInter_sub _ _

def sub_iSup (a: Set α) (s: ι -> Set α): a ∈ range s -> a ⊆ iSup s := by
  intro eq
  apply sub_trans _ (sub_sSup _ _ _)
  exact a
  rfl
  assumption

def iInf_sub (a: Set α) (s: ι -> Set α): a ∈ range s -> iInf s ⊆ a := by
  intro eq
  apply sub_trans (sInf_sub _ _ _)
  rfl
  assumption

instance : SDiff (Set α) where
  sdiff a b := a ∩ bᶜ

def mem_sdiff {a b: Set α} : ∀{x}, x ∈ a \ b ↔ x ∈ a ∧ x ∉ b := by rfl

def univ_sub (a: Set α) : univ α ⊆ a -> a = univ α := by
  intro sub
  apply ext_univ
  intro x
  apply sub
  apply mem_univ

@[simp]
def sub_univ (s: Set α) : s ⊆ univ α := by
  intros _ _
  apply mem_univ

def sub_empty (s: Set α) : s ⊆ ∅ -> s = ∅ := ext_empty s
@[simp]
def empty_sub (s: Set α) : ∅ ⊆ s := fun _ mem => (not_mem_empty mem).elim

def compl_compl (s: Set α) : sᶜᶜ = s := by
  ext x
  apply Iff.intro
  intro h
  exact Classical.not_not.mp h
  intro h g
  exact g h

def inter_comm (a b: Set α) : a ∩ b = b ∩ a := by
  ext x
  simp [mem_inter, And.comm]

def union_comm (a b: Set α) : a ∪ b = b ∪ a := by
  ext x
  simp [mem_union, Or.comm]

def inter_assoc (a b c: Set α) : a ∩ b ∩ c = a ∩ (b ∩ c) := by
  ext x
  simp [mem_inter, and_assoc]

def union_assoc (a b c: Set α) : a ∪ b ∪ c = a ∪ (b ∪ c) := by
  ext x
  simp [mem_union, or_assoc]

instance : Subsingleton (∅: Set α).Elem where
  allEq := by
    intro x
    exact x.property.elim

instance : Subsingleton ({a}: Set α).Elem where
  allEq := by
    intro ⟨x, hx⟩ ⟨y, hy⟩
    cases hx; cases hy
    rfl

@[simp]
def sInter_insert (a: Set α) (as: Set (Set α)) : ⋂(insert  a as) = a ∩ ⋂as := by
   ext x
   simp [mem_sInter, mem_inter, mem_insert]

@[simp]
def sUnion_insert (a: Set α) (as: Set (Set α)) : ⋃(insert  a as) = a ∪ ⋃as := by
  ext x
  simp [mem_sUnion, mem_union, mem_insert]

def inter_sub_left (a b: Set α) : a ∩ b ⊆ a := by
  intro x mem
  exact (mem_inter.mp mem).left
def inter_sub_right (a b: Set α) : a ∩ b ⊆ b := by
  intro x mem
  exact (mem_inter.mp mem).right

def sub_def (a b: Set α) : (a ⊆ b) = ∀x ∈ a, x ∈ b := rfl

def sub_inter (a b k: Set α) : (k ⊆ a ∧ k ⊆ b) ↔ k ⊆ a ∩ b := by
  apply Iff.intro
  intro h x xmem
  simp [mem_inter, h.left _ xmem, h.right _ xmem]
  intro h
  apply And.intro <;> (intro x xmem; simp [mem_inter.mp (h x xmem)])

def sub_union_left (a b: Set α) : a ⊆ a ∪ b := fun _ => .inl
def sub_union_right (a b: Set α) : b ⊆ a ∪ b := fun _ => .inr

@[simp]
def mk_mem (P: α -> Prop) : ∀{x}, x ∈ mk P ↔ P x := by rfl

def union_sub (a b k: Set α) : (a ⊆ k ∧ b ⊆ k) ↔ a ∪ b ⊆ k := by
  apply Iff.intro
  intro ⟨ha, hb⟩  x xmem
  rw [mem_union] at xmem
  rcases xmem with hxa | hxb
  exact ha _ hxa; exact hb _ hxb
  intro h
  apply And.intro
  intro x ha
  exact h _ (.inl ha)
  intro x hb
  exact h _ (.inr hb)

@[simp]
def univ_inter (a: Set α) : univ α ∩ a = a := by
  ext x
  simp [mem_inter, mem_univ]
@[simp]
def inter_univ (a: Set α) : a ∩ univ α = a := by
  ext x
  simp [mem_inter, mem_univ]

@[simp]
def univ_union (a: Set α) : univ α ∪ a = univ α := by
  ext x
  simp [mem_union, mem_univ]
@[simp]
def union_univ (a: Set α) : a ∪ Set.univ α = univ α := by
  ext x
  simp [mem_union, mem_univ]

@[simp]
def empty_inter (a: Set α) : ∅ ∩ a = ∅ := by
  apply ext_empty
  intro x
  simp [mem_inter]; intro; contradiction
@[simp]
def inter_empty (a: Set α) : a ∩ ∅ = ∅ := by
  simp [inter_comm a]

@[simp]
def empty_union (a: Set α) : ∅ ∪ a = a := by
  ext x
  simp [mem_union]; intro; contradiction
@[simp]
def union_empty (a: Set α) : a ∪ ∅ = a := by
  simp [union_comm a]

def mem_pair {a b: α} : ∀{x}, x ∈ ({a, b}: Set α) ↔ x = a ∨ x = b := by rfl

def singleton_eq_insert_empty (a: α) : {a} = insert a (∅: Set _) := by
  ext x
  simp [mem_singleton, mem_insert]
  intro; contradiction

@[simp]
def sUnion_singleton (s: Set α) : ⋃({s}: Set _) = s := by
  simp [singleton_eq_insert_empty]

@[simp]
def sInter_singleton (s: Set α) : ⋂({s}: Set _) = s := by
  simp [singleton_eq_insert_empty]

def inter_sInter_sub_sInter_inter (a b: Set (Set α)) : ⋂a ∩ ⋂b ⊆ ⋂(a ∩ b) := by
  intro x mem
  simp [mem_sInter, mem_inter] at *
  obtain ⟨ha, hb⟩ := mem
  intro y ya yb
  apply ha
  assumption

def inter_sub_inter (a b c d: Set α) : a ⊆ c -> b ⊆ d -> a ∩ b ⊆ c ∩ d := by
  intro ac bd
  intro x
  simp [mem_inter]
  intro ha hb
  apply And.intro
  apply ac; assumption
  apply bd; assumption

def sInter_union (a b: Set (Set α)) : ⋂(a ∪ b) = ⋂a ∩ ⋂b := by
  ext x
  simp [mem_sInter, mem_union, mem_inter]
  apply Iff.intro
  intro h
  apply And.intro
  intro y mem
  apply h
  left; assumption
  intro y mem
  apply h
  right; assumption
  intro ⟨ha, hb⟩ y mem
  cases mem
  apply ha; assumption
  apply hb; assumption

def sUnion_union (a b: Set (Set α)) : ⋃(a ∪ b) = ⋃a ∪ ⋃b := by
  ext x
  simp [mem_sUnion, mem_union]
  apply Iff.intro
  intro ⟨x', h, mem⟩
  cases h
  left
  exists x'
  right
  exists x'
  intro h
  rcases h with ⟨x', _, h⟩ | ⟨x', _, h⟩ <;>(
    exists x'
    apply And.intro _ h)
  left; assumption
  right; assumption

def singleton_sub (a: α) (b: Set α) : {a} ⊆ b ↔ a ∈ b := by
  simp [sub_def, mem_singleton]

def inter_union_right (a b k: Set α) : (a ∪ b) ∩ k = a ∩ k ∪ b ∩ k := by
  ext x
  simp  [mem_union, mem_inter, or_and_right]

def inter_union_left (a b k: Set α) : k ∩ (a ∪ b) = k ∩ a ∪ k ∩ b := by
  simp [inter_comm k, inter_union_right]

def union_inter_right (a b k: Set α) : (a ∩ b) ∪ k = (a ∪ k) ∩ (b ∪ k) := by
  ext x
  simp  [mem_union, mem_inter, and_or_right]

def union_inter_left (a b k: Set α) : k ∪ (a ∩ b) = (k ∪ a) ∩ (k ∪ b) := by
  simp [union_comm k, union_inter_right]

instance : @Std.Commutative (Set α) (· ∩ ·) := ⟨inter_comm⟩
instance : @Std.Associative (Set α) (· ∩ ·) := ⟨inter_assoc⟩
instance : @Std.Commutative (Set α) (· ∪ ·) := ⟨union_comm⟩
instance : @Std.Associative (Set α) (· ∪ ·) := ⟨union_assoc⟩

@[simp]
def pair_image (a b: α) (f: α -> β) : Set.image {a, b} f = {f a, f b} := by
  ext x
  simp [mem_pair, mem_image]

@[simp]
def sInter_pair (a b: Set α) : ⋂({a, b}: Set _) = a ∩ b := by
  ext x
  simp

@[simp]
def sUnion_pair (a b: Set α) : ⋃({a, b}: Set _) = a ∪ b := by
  ext x
  simp

def attach (s: Set α) : Set s := .univ _

def mem_attach {s: Set α} : ∀{x}, x ∈ s.attach ↔ x.val ∈ s := by
  intro x
  simp [mem_univ, attach, x.property]

@[simp]
def pair_attach {a b: α} : ({a, b}: Set α).attach = {⟨a, mem_pair.mpr (.inl rfl)⟩, ⟨b, mem_pair.mpr (.inr rfl)⟩} := by
  ext x
  cases x with | mk x mem =>
  simp [mem_pair, mem_attach, mem]
  cases mem_pair.mp mem
  subst x; left; rfl
  subst x; right; rfl

@[simp]
def inter_self (a: Set α) : a ∩ a = a := by
  ext x
  simp [mem_inter]
@[simp]
def union_self (a: Set α) : a ∪ a = a := by
  ext x
  simp [mem_union]

def image_const_of_nonempty (a: Set α) (b: β) : a.Nonempty -> a.image (fun _ => b) = {b} := by
  intro ⟨a', ha'⟩
  ext x
  simp [mem_image, mem_singleton]
  intro h
  exists a'

def nonempty_insert {a: Set α} {x: α} : (insert x a: Set α).Nonempty :=
  ⟨x, Set.mem_insert.mpr (.inl rfl)⟩

def nonempty_attach (a: Set α) : a.attach.Nonempty ↔ a.Nonempty := by
  apply Iff.intro
  intro ⟨⟨x, _⟩,  _⟩
  exists x
  intro ⟨x, h⟩
  exists ⟨x, h⟩

def not_nonempty (a: Set α) (h: ¬a.Nonempty) : a = ∅ := by
  apply ext_empty
  intro x hx
  apply h
  exists x

@[simp]
def empty_attach : (∅: Set α).attach = ∅ := by
  apply ext_empty
  intro ⟨_, _⟩
  contradiction

@[simp]
def empty_image : (∅: Set α).image f = ∅ := by
  apply ext_empty
  intro x h
  have ⟨_, _, _⟩  := mem_image.mp h
  contradiction

def has_min (r: α -> α -> Prop) (wf: WellFounded r) (s: Set α) (h: s.Nonempty):
  ∃x ∈ s, ∀y ∈ s, ¬r y x := by
  obtain ⟨x, mem⟩ := h
  induction x using wf.induction with
  | h x ih =>
  by_cases h:∃y ∈ s, r y x
  obtain ⟨y, y_in_s, ryx⟩ := h
  exact ih y ryx y_in_s
  refine ⟨x, mem, ?_⟩
  intro y ymem
  exact (h ⟨y, ⟨ymem, ·⟩⟩)

def range_comp {f: α -> β} {g: β -> γ} :
  x ∈ Set.range f ->
  g x ∈ Set.range (g ∘ f) := by
  intro mem
  apply Set.mem_range.mpr
  obtain ⟨a', eq⟩  := Set.mem_range.mp mem
  exact ⟨a', eq ▸ rfl⟩

def mem_range' {f: α -> β} :
  f x ∈ Set.range f := by
  apply Set.mem_range.mpr
  exists x

def ssub_spec {a b: Set α} (h: a ⊂ b) : ∃x ∈ b, x ∉ a := by
  apply Classical.byContradiction
  intro g
  rw [not_exists] at g
  replace g := fun x => not_and.mp (g x)
  apply h.left
  apply sub_antisymm h.right
  intro x mem
  apply Classical.not_not.mp
  apply g
  assumption

instance : IsEmpty (Elem (∅: Set α)) where
  elim x := not_mem_empty x.property

def support_by (f: α -> β) (default: β): Set α := (Set.preimage {default} f)ᶜ
def support (f: α -> β) [Zero β] := support_by f 0

def mem_support_by {f: α -> β} {default: β}: ∀{x}, x ∈ support_by f default ↔ f x ≠ default := Iff.rfl
def mem_support {f: α -> β} [Zero β]: ∀{x}, x ∈ support f ↔ f x ≠ 0 := Iff.rfl

def support_by_const_default (default: β) :
  Set.support_by (fun _: α => default) default = ∅ := by
  apply ext_empty
  intros x mem
  contradiction

def support_const_zero [Zero β] :
  Set.support (fun _: α => (0: β)) = ∅ := support_by_const_default 0

def support_by_const_ne_default {value default: β} (h: value ≠ default) :
  Set.support_by (fun _: α => value) default = Set.univ _ := by
  apply ext_univ
  intro x
  assumption

def support_const_ne_zero [Zero β] {value: β} (h: value ≠ 0) :
  Set.support (fun _: α => value) = Set.univ _ := support_by_const_ne_default h

@[coe]
def ofList (xs: List α) := Set.mk (· ∈ xs)

instance : Coe (List α) (Set α) := ⟨ofList⟩

instance : Top (Set α) where
  top := Set.univ _
instance : Bot (Set α) where
  bot := ∅

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

def image_id (s: Set α) : s.image id = s := by
  ext x
  rw [mem_image]
  apply Iff.intro
  intro ⟨_, _, eq⟩
  cases eq
  assumption
  intro
  exists x

def image_image (s: Set α) (f: α -> β) (g: β -> γ) : (s.image f).image g = s.image (g ∘ f) := by
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

def preimage_preimage (s: Set α) (f: γ -> β) (g: β -> α) : (s.preimage g).preimage f = s.preimage (g ∘ f) := by
  rfl

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

def image_preimage (s: Set α) (f: α -> β) (h: Function.Injective f) : (s.image f).preimage f = s := by
  ext x
  rw [mem_preimage, mem_image]
  apply Iff.intro
  intro ⟨y, mem, eq⟩
  cases h eq
  assumption
  intro mem
  exists x

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

def prod (a: Set α) (b: Set β) : Set (α × β) := Set.mk fun x => x.fst ∈ a ∧ x.snd ∈ b

def image_empty : Set.image ∅ f = ∅ := by
  apply ext_empty
  intro x ⟨_, _, _⟩
  contradiction

def image_insert (a: α) (as: Set α) : (insert a as: Set α).image f = (insert (f a) (as.image f)) := by
  ext x
  apply Iff.intro
  intro ⟨_, mem, _⟩
  rw [mem_insert] at *
  cases mem
  left;
  subst a
  assumption
  right
  subst x
  apply Set.mem_image'
  assumption
  rw [mem_insert]
  intro mem
  cases mem
  subst x
  apply Set.mem_image'
  apply mem_insert.mpr
  left; rfl
  rename_i h
  obtain ⟨y, _, _⟩ := h
  exists y; subst x
  apply And.intro _ rfl
  rw [mem_insert]
  right; assumption

def image_pair (a b: α) : ({a, b}: Set α).image f = ({f a, f b}: Set _) := by
  rw [image_insert, singleton_eq_insert_empty, image_insert, image_empty,
    ←singleton_eq_insert_empty]

def compl_subset_compl {s t: Set α} : sᶜ ⊆ tᶜ ↔ t ⊆ s := by
  apply Iff.intro
  intro h x mem
  exact Classical.not_not.mp (h x · mem)
  intro h x mem mem'
  apply mem
  apply h
  assumption

def image_subset {a b : Set α} (f : α → β) (h : a ⊆ b) : a.image f ⊆ b.image f := by
  intro x ⟨y, mem, eq⟩
  subst eq
  apply Set.mem_image'
  apply h
  assumption

open Classical in
def compl_injective {a b: Set α} : aᶜ = bᶜ -> a = b := by
  intro h
  ext x
  apply Decidable.not_iff_not.mp
  rw [←mem_compl, h]
  rfl

open Classical in
noncomputable
def piecewise (s: Set α) (f g: α -> β) : α -> β :=
  fun x => if x ∈ s then f x else g x

def range_iff_surjective (f: α -> β) : Set.range f = ⊤ ↔ Function.Surjective f := by
  apply Iff.intro
  intro eq x
  have : x ∈ range f := by rw [eq]; trivial
  assumption
  intro h
  ext x
  apply Iff.intro; intro; trivial
  intro
  apply h

def range_piecewise (s: Set α) (f: α -> β) (g: α -> β)  :
  Set.range (s.piecewise f g) = s.image f ∪ sᶜ.image g := by
  ext x
  rw [Set.mem_union, Set.mem_image, Set.mem_image]
  apply Iff.intro
  intro ⟨y, eq⟩
  subst x
  unfold piecewise
  by_cases h:y ∈ s
  left
  refine ⟨_, h, ?_⟩
  rw [if_pos h]
  right
  refine ⟨_, h, ?_⟩
  rw [if_neg h]
  intro h
  unfold piecewise
  rcases h with ⟨y, mem, eq⟩ | ⟨y, mem, eq⟩
  exists y
  dsimp; rw [if_pos mem]; assumption
  exists y
  dsimp; rw [if_neg mem]; assumption

def union_compl (s: Set α) : s ∪ sᶜ = ⊤ := by
  ext x; classical
  rw [Set.mem_union, Set.mem_compl]
  apply Iff.intro <;> intro
  trivial
  exact Decidable.or_not_self _

section min_elem

variable (r: α -> α -> Prop) [Relation.IsWellFounded r]
variable {s: Set α} (h: s.Nonempty)

def exists_min_elem:
  ∃x ∈ s, ∀y ∈ s, ¬r y x := by
  obtain ⟨x, mem, spec⟩ := Relation.exists_min r h
  refine ⟨x, mem, ?_⟩
  intro y y_in_s ryx
  apply spec
  assumption
  assumption

noncomputable def min := Classical.choose (exists_min_elem r h)
noncomputable def min_mem : min r h ∈ s := (Classical.choose_spec (exists_min_elem r h)).left
noncomputable def not_lt_min : ∀y ∈ s, ¬r y (min r h) := (Classical.choose_spec (exists_min_elem r h)).right

end min_elem

end Set
