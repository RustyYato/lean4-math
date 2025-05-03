import Math.Data.Set.Basic
import Math.Data.Set.TopBot

open Set hiding Nonempty

section

class ConditionallyCompleteLatticeOps (α: Type*) extends LatticeOps α, SupSet α, InfSet α where

instance [LE α] [LT α] [Min α] [Max α] [SupSet α] [InfSet α] : ConditionallyCompleteLatticeOps α where

variable (α: Type*) [Max α] [Min α] [SupSet α] [InfSet α] [LE α] [LT α]

class IsConditionallyCompleteLattice : Prop extends IsLattice α where
  le_csSup : ∀{s} {a: α}, BoundedAbove s → a ∈ s → a ≤ (⨆ s)
  csSup_le : ∀{s} {a: α}, Set.Nonempty s → a ∈ upperBounds s → ⨆ s ≤ a
  csInf_le : ∀{s} {a: α}, BoundedBelow s → a ∈ s → ⨅ s ≤ a
  le_csInf : ∀{s} {a: α}, Set.Nonempty s → a ∈ lowerBounds s → a ≤ ⨅ s

export IsConditionallyCompleteLattice (le_csSup csSup_le csInf_le le_csInf)

instance [IsConditionallyCompleteLattice α] : IsConditionallyCompleteLattice (Opposite α) where
  le_csSup := csInf_le (α := α)
  csSup_le := le_csInf (α := α)
  csInf_le := le_csSup (α := α)
  le_csInf := csSup_le (α := α)

end

variable {α: Type*} [Max α] [Min α] [SupSet α] [InfSet α] [LE α] [LT α]
variable {a b c: α} {s t: Set α} [IsConditionallyCompleteLattice α]

def le_csSup_of_le (hs : BoundedAbove s) (hb : b ∈ s) (h : a ≤ b) : a ≤ ⨆ s :=
  le_trans h (le_csSup hs hb)

def csInf_le_of_le (hs : BoundedBelow s) (hb : b ∈ s) (h : b ≤ a) : ⨅ s ≤ a :=
  le_trans (csInf_le hs hb) h

def csSup_le_csSup (ht : BoundedAbove t) (hs : s.Nonempty) (h : s ⊆ t) : ⨆ s ≤ ⨆ t :=
  csSup_le hs fun _ ha => le_csSup ht (h _ ha)

def csInf_le_csInf (ht : BoundedBelow t) (hs : s.Nonempty) (h : s ⊆ t) : ⨅ t ≤ ⨅ s :=
  csSup_le_csSup (α := Opposite α) ht hs h

def le_csSup_iff (h : BoundedAbove s) (hs : s.Nonempty) :
    a ≤ ⨆ s ↔ ∀ b, b ∈ upperBounds s → a ≤ b := by
  apply Iff.intro
  intro h _ hb
  exact le_trans h (csSup_le hs hb)
  intro hb
  apply hb
  intro
  exact le_csSup h

def csInf_le_iff (h : BoundedBelow s) (hs : s.Nonempty) : ⨅ s ≤ a ↔ ∀ b ∈ lowerBounds s, b ≤ a :=
  le_csSup_iff (α := Opposite α) h hs

def isLUB_csSup (ne : s.Nonempty) (H : BoundedAbove s) : IsLUB s (⨆ s) :=
  ⟨fun _ => le_csSup H, fun _ => csSup_le ne⟩

def isLUB_ciSup [Nonempty ι] {f : ι → α} (H : BoundedAbove (range f)) :
    IsLUB (range f) (⨆i, f i) :=
  isLUB_csSup (nonempty_range f) H

def isLUB_ciSup_set {f : β → α} {s : Set β} (H : BoundedAbove (s.image f)) (Hne : s.Nonempty) :
    IsLUB (s.image f) (⨆i: s, f i) := by
  rw [← sSup_image']
  exact isLUB_csSup (nonimage_empty Hne _) H

def isGLB_csInf (ne : s.Nonempty) (H : BoundedBelow s) : IsGLB s (⨅ s) :=
  isLUB_csSup (α := Opposite α) ne H

def isGLB_ciInf [Nonempty ι] {f : ι → α} (H : BoundedBelow (range f)) :
    IsGLB (range f) (⨅i, f i) := isLUB_ciSup (α := Opposite α) H

def isGLB_ciInf_set {f : β → α} {s : Set β} (H : BoundedBelow (s.image f)) (Hne : s.Nonempty) :
    IsGLB (s.image f) (⨅i: s, f i) :=
  isLUB_ciSup_set (α := Opposite α) H Hne

def ciSup_le_iff [Nonempty ι] {f : ι → α} {a : α} (hf : BoundedAbove (range f)) :
    ⨆i, f i ≤ a ↔ ∀ i, f i ≤ a :=
  (isLUB_le_iff <| isLUB_ciSup hf).trans forall_mem_range

def le_ciInf_iff [Nonempty ι] {f : ι → α} {a : α} (hf : BoundedBelow (range f)) :
    a ≤ ⨅i, f i ↔ ∀ i, a ≤ f i := ciSup_le_iff (α := Opposite α) hf

def ciSup_set_le_iff {ι : Type*} {s : Set ι} {f : ι → α} {a : α} (hs : s.Nonempty)
    (hf : BoundedAbove (s.image f)) : ⨆i: s, f i ≤ a ↔ ∀ i ∈ s, f i ≤ a :=
  (isLUB_le_iff <| isLUB_ciSup_set hf hs).trans forall_mem_image

def le_ciInf_set_iff {ι : Type*} {s : Set ι} {f : ι → α} {a : α} (hs : s.Nonempty)
    (hf : BoundedBelow (s.image f)) : (a ≤ ⨅i: s, f i) ↔ ∀ i ∈ s, a ≤ f i :=
  ciSup_set_le_iff (α := Opposite α) hs hf

def csSup_le_iff (hb : BoundedAbove s) (hs : s.Nonempty) : ⨆ s ≤ a ↔ ∀ b ∈ s, b ≤ a :=
  isLUB_le_iff (isLUB_csSup hs hb)

def le_csInf_iff (hb : BoundedBelow s) (hs : s.Nonempty) : a ≤ ⨅ s ↔ ∀ b ∈ s, a ≤ b :=
  le_isGLB_iff (isGLB_csInf hs hb)

def lt_csSup_of_lt (hs : BoundedAbove s) (ha : a ∈ s) (h : b < a) : b < ⨆ s :=
  lt_of_lt_of_le h (le_csSup hs ha)

def csInf_lt_of_lt : BoundedBelow s → a ∈ s → a < b → ⨅ s < b :=
  lt_csSup_of_lt (α := Opposite α)

def csSup_singleton (a : α) : ⨆ {a} = a := by
  apply le_antisymm
  apply csSup_le
  exact Set.nonempty_singleton _
  intro x h
  cases Set.mem_singleton.mp h
  rfl
  apply le_csSup
  exists a
  intro x h
  cases Set.mem_singleton.mp h
  rfl
  rfl

def csInf_singleton (a : α) : ⨅ {a} = a :=
  csSup_singleton (α := Opposite α) a

def csSup_union (hs : BoundedAbove s) (sne : s.Nonempty) (ht : BoundedAbove t) (tne : t.Nonempty) :
  sSup (s ∪ t) = (⨆ s) ⊔ ⨆ t := by
  have : (⨆ s) ⊔ ⨆ t ∈ upperBounds (s ∪ t) := by
    intro x mem
    cases Set.mem_union.mp mem <;> rename_i mem
    apply flip le_trans
    apply le_max_left
    apply le_csSup
    assumption
    assumption
    apply flip le_trans
    apply le_max_right
    apply le_csSup
    assumption
    assumption
  have : BoundedAbove (s ∪ t) := ⟨_, this⟩
  have : Set.Nonempty (s ∪ t) := nonempty_union_left sne
  apply le_antisymm
  apply (csSup_le_iff _ _).mpr
  intro x mem
  cases mem
  apply flip le_trans
  apply le_max_left
  apply le_csSup
  assumption
  assumption
  apply flip le_trans
  apply le_max_right
  apply le_csSup
  repeat assumption
  apply max_le_iff.mpr
  apply And.intro
  apply csSup_le_csSup
  assumption
  assumption
  apply Set.sub_union_left
  apply csSup_le_csSup
  assumption
  assumption
  apply Set.sub_union_right

def csInf_union (hs : BoundedBelow s) (sne : s.Nonempty) (ht : BoundedBelow t) (tne : t.Nonempty) :
  ⨅ (s ∪ t) = (⨅ s) ⊓ (⨅ t) := csSup_union (α := Opposite α) hs sne ht tne

def csSup_insert {a: α} {as: Set α} (ha: BoundedAbove as) (ne: as.Nonempty) : ⨆ (insert a as) = a ⊔ ⨆ as := by
  rw [insert_eq, csSup_union, csSup_singleton]
  apply BoundedAbove.singleton
  exact Set.nonempty_singleton _
  assumption
  assumption

def csInf_insert {a: α} {as: Set α} (ha: BoundedBelow as) (ne: as.Nonempty) : ⨅ (insert a as) = a ⊓ ⨅ as :=
  csSup_insert (α := Opposite α) ha ne

def csSup_pair (a b : α) : ⨆ {a, b} = a ⊔ b := by
  rw [csSup_insert, csSup_singleton]
  apply BoundedAbove.singleton
  exact Set.nonempty_singleton _

def csInf_pair (a b : α) : ⨅ {a, b} = a ⊓ b :=
  csSup_pair (α := Opposite α) a b

def csSup_inter_le (hs: BoundedAbove s) (ht: BoundedAbove t) (ne : (s ∩ t).Nonempty):
  sSup (s ∩ t) ≤ (⨆ s) ⊓ ⨆ t := by
  have : BoundedAbove (s ∩ t) := by
    obtain ⟨x, hs⟩ := hs
    exists x
    intro y mem
    apply hs
    exact mem.left
  apply le_min_iff.mpr
  apply And.intro
  apply csSup_le_csSup
  assumption
  assumption
  apply Set.inter_sub_left
  apply csSup_le_csSup
  assumption
  assumption
  apply Set.inter_sub_right

def le_csInf_inter (hs: BoundedBelow s) (ht: BoundedBelow t) (ne : (s ∩ t).Nonempty):
  (⨅ s) ⊔ ⨅ t ≤ ⨅ (s ∩ t) :=
  csSup_inter_le (α := Opposite α) hs ht ne

def ciSup_le [Nonempty ι] {f : ι → α} {c : α} (H : ∀ x, f x ≤ c) : ⨆i, f i ≤ c :=
  csSup_le (nonempty_range f) (by rwa [mem_upperBounds, forall_mem_range])

def le_ciInf [Nonempty ι] {f : ι → α} {c : α} (H : ∀ x, c ≤ f x) : c ≤ ⨅i, f i :=
  ciSup_le (α := Opposite α) H

def le_ciSup {f : ι → α} (H : BoundedAbove (range f)) (c : ι) : f c ≤ ⨆i, f i :=
  le_csSup H Set.mem_range'

def ciInf_le {f : ι → α} (H : BoundedBelow (range f)) (c : ι) : ⨅i, f i ≤ f c :=
  csInf_le H Set.mem_range'

def not_mem_of_lt_csInf {x : α} {s : Set α} (h : x < ⨅ s) (hs : BoundedBelow s) : x ∉ s :=
  fun hx => lt_irrefl (lt_of_lt_of_le h (csInf_le hs hx))

def not_mem_of_csSup_lt {x : α} {s : Set α} (h : ⨆ s < x) (hs : BoundedAbove s) : x ∉ s :=
  not_mem_of_lt_csInf (α := Opposite α) h hs

namespace Set

theorem IsGLB.csInf_eq (H : IsGLB s a) (ne : s.Nonempty) : ⨅ s = a :=
  (isGLB_csInf ne ⟨a, H.1⟩).unique H

def IsLeast.csInf_eq (H : IsLeast s a) : ⨅ s = a :=
  H.isGLB.csInf_eq H.nonempty

end Set

section

variable [SupSet α] [InfSet α] [Max α] [Min α] [LE α] [LT α]
variable [IsPartialOrder α] [@Relation.IsWellFounded α (· < ·)] [@Relation.IsConnected α (· < ·)]
variable {a b c: α} {s t: Set α} [IsConditionallyCompleteLattice α]

variable [IsConditionallyCompleteLattice α]

def sInf_eq_argmin_on (hs : s.Nonempty) :
  have : Nonempty s := by
    obtain ⟨x, h⟩ := hs
    exact ⟨x, h⟩
  ⨅ s = Relation.argMin (fun x: s => x.val) (· < ·) := by
  have : Nonempty s := by
    obtain ⟨x, h⟩ := hs
    exact ⟨x, h⟩
  apply IsLeast.csInf_eq
  apply And.intro
  apply Subtype.property
  intro a ha
  have ⟨h, spec⟩ := Classical.choose_spec (Relation.exists_min (fun x y: s => x.val < y.val) (P := fun _ => True) ⟨⟨a, ha⟩, True.intro⟩)
  dsimp at spec; clear h
  have := spec ⟨a, ha⟩
  conv at this => { rhs; rw [not_true] }
  exact le_of_not_lt this

def csInf_mem (hs : s.Nonempty) : ⨅ s ∈ s := by
  rw [sInf_eq_argmin_on]
  apply Subtype.property
  assumption

def ciInf_mem [Nonempty ι] (f : ι → α) : ⨅i, f i ∈ range f :=
  csInf_mem (nonempty_range f)

end
