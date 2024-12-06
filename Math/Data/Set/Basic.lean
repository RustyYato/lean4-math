import Math.Type.Basic
import Math.Function.Basic

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

@[refl]
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

def sUnion (a: Set α) [Membership β α] : Set β := .mk fun x => ∃a' ∈ a, x ∈ a'
instance [Membership β α] : SUnion (Set α) (Set β) := ⟨(·.sUnion)⟩
def mem_sUnion {a: Set α} [Membership β α] : ∀{x}, x ∈ ⋃ a ↔ ∃a' ∈ a, x ∈ a' := Iff.refl _

def sInter (a: Set α) [Membership β α] : Set β := .mk fun x => ∀a' ∈ a, x ∈ a'
instance [Membership β α] : SInter (Set α) (Set β) := ⟨(·.sInter)⟩
def mem_sInter {a: Set α} [Membership β α] : ∀{x}, x ∈ ⋂ a ↔ ∀a' ∈ a, x ∈ a' := Iff.refl _

def sUnion_empty [Membership β α] : ⋃(∅: Set α) = ∅ := by
  apply ext_empty
  intro x
  rw [mem_sUnion]
  intro ⟨_, _, _⟩
  contradiction

def sInter_empty [Membership β α] : ⋂(∅: Set α) = univ _ := by
  apply ext_univ
  intro x
  rw [mem_sInter]
  intros
  contradiction

def preimage (a: Set α) (f: β -> α) : Set β := mk fun x => ∃a' ∈ a, a' = f x
def mem_preimage {a: Set α} {f: β -> α} : ∀{x}, x ∈ a.preimage f ↔ ∃a' ∈ a, a' = f x := Iff.refl _
def image (a: Set α) (f: α -> β) : Set β := mk fun x => ∃a' ∈ a, x = f a'
def mem_image {a: Set α} {f: α -> β} : ∀{x}, x ∈ a.image f ↔ ∃a' ∈ a, x = f a' := Iff.refl _
def range (f: α -> β) : Set β := image (univ _) f
def mem_range {f: α -> β} : ∀{x}, x ∈ range f ↔ ∃a', x = f a' := by
  intro x
  apply Iff.trans mem_image
  simp [mem_univ]

def powerset (a: Set α) : Set (Set α) := mk fun x => x ⊆ a
def mem_powerset {a: Set α} : ∀{x}, x ∈ a.powerset ↔ x ⊆ a := Iff.refl _

def compl (a: Set α) : Set α := mk fun x => x ∉ a
instance : SetComplement (Set α) where
  scompl := compl
def mem_compl {a: Set α} : ∀{x}, x ∈ aᶜ ↔ x ∉ a := Iff.refl _

def Nonempty (a: Set α) := ∃x, x ∈ a
def Elem (a: Set α) := { x // x ∈ a }

instance : Singleton α (Set α) where
  singleton a := mk fun x => x = a
def mem_singleton {a: α}: ∀{x}, x ∈ ({a}: Set α) ↔ x = a := Iff.refl _

instance : Insert α (Set α) where
  insert a x := {a} ∪ x
def mem_insert {a: α} {as: Set α}: ∀{x}, x ∈ Insert.insert a as ↔ x = a ∨ x ∈ as := Iff.refl _

end Set
