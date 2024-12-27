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

def sUnion (a: Set (Set α)) : Set α := .mk fun x => ∃a' ∈ a, x ∈ a'
instance : SUnion (Set (Set α)) (Set α) := ⟨(·.sUnion)⟩
def mem_sUnion {a: Set (Set α)} : ∀{x}, x ∈ ⋃ a ↔ ∃a' ∈ a, x ∈ a' := Iff.refl _

def sInter (a: Set (Set α)) : Set α := .mk fun x => ∀a' ∈ a, x ∈ a'
instance : SInter (Set (Set α)) (Set α) := ⟨(·.sInter)⟩
def mem_sInter {a: Set (Set α)} : ∀{x}, x ∈ ⋂ a ↔ ∀a' ∈ a, x ∈ a' := Iff.refl _

def sUnion_empty : ⋃(∅: Set (Set α)) = ∅ := by
  apply ext_empty
  intro x
  rw [mem_sUnion]
  intro ⟨_, _, _⟩
  contradiction

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

def univ_compl : (Set.univ α)ᶜ = ∅ := by
  apply ext_empty
  intro x h
  exact h True.intro

def empty_compl : ∅ᶜ = Set.univ α := by
  apply ext_univ
  intro x h
  contradiction

def Nonempty (a: Set α) := ∃x, x ∈ a
def Elem (a: Set α) := { x // x ∈ a }

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

def sub_univ (s: Set α) : s ⊆ univ α := by
  intros _ _
  apply mem_univ

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

instance : Subsingleton (∅: Set α).Elem where
  allEq := by
    intro x
    exact x.property.elim

instance : Subsingleton ({a}: Set α).Elem where
  allEq := by
    intro ⟨x, hx⟩ ⟨y, hy⟩
    cases hx; cases hy
    rfl

def sInter_insert (a: Set α) (as: Set (Set α)) : ⋂(insert  a as) = a ∩ ⋂as := by
   ext x
   simp [mem_sInter, mem_inter, mem_insert]

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

end Set
