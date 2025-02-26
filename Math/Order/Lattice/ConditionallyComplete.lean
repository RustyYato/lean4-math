import Math.Order.Lattice.Basic
import Math.Data.Set.Basic
import Math.Data.Set.TopBot

open Set hiding Nonempty

section

variable (α: Type*) [Sup α] [Inf α] [SupSet α] [InfSet α] [LE α] [LT α]

class IsConditionallyCompleteLattice : Prop extends IsLattice α where
  le_csSup : ∀{s} {a: α}, BoundedAbove s → a ∈ s → a ≤ sSup s
  csSup_le : ∀{s} {a: α}, Set.Nonempty s → a ∈ upperBounds s → sSup s ≤ a
  csInf_le : ∀{s} {a: α}, BoundedBelow s → a ∈ s → sInf s ≤ a
  le_csInf : ∀{s} {a: α}, Set.Nonempty s → a ∈ lowerBounds s → a ≤ sInf s

export IsConditionallyCompleteLattice (le_csSup csSup_le csInf_le le_csInf)

instance [IsConditionallyCompleteLattice α] : IsConditionallyCompleteLattice (Opposite α) where
  le_csSup := csInf_le (α := α)
  csSup_le := le_csInf (α := α)
  csInf_le := le_csSup (α := α)
  le_csInf := csSup_le (α := α)

end

variable {α: Type*} [Sup α] [Inf α] [SupSet α] [InfSet α] [LE α] [LT α]
variable {a b c: α} {s t: Set α} [IsConditionallyCompleteLattice α]

def le_csSup_of_le (hs : BoundedAbove s) (hb : b ∈ s) (h : a ≤ b) : a ≤ sSup s :=
  le_trans h (le_csSup hs hb)

def csInf_le_of_le (hs : BoundedBelow s) (hb : b ∈ s) (h : b ≤ a) : sInf s ≤ a :=
  le_trans (csInf_le hs hb) h

def csSup_le_csSup (ht : BoundedAbove t) (hs : s.Nonempty) (h : s ⊆ t) : sSup s ≤ sSup t :=
  csSup_le hs fun _ ha => le_csSup ht (h _ ha)

def csInf_le_csInf (ht : BoundedBelow t) (hs : s.Nonempty) (h : s ⊆ t) : sInf t ≤ sInf s :=
  csSup_le_csSup (α := Opposite α) ht hs h

def le_csSup_iff (h : BoundedAbove s) (hs : s.Nonempty) :
    a ≤ sSup s ↔ ∀ b, b ∈ upperBounds s → a ≤ b := by
  apply Iff.intro
  intro h _ hb
  exact le_trans h (csSup_le hs hb)
  intro hb
  apply hb
  intro
  exact le_csSup h

def csInf_le_iff (h : BoundedBelow s) (hs : s.Nonempty) : sInf s ≤ a ↔ ∀ b ∈ lowerBounds s, b ≤ a :=
  le_csSup_iff (α := Opposite α) h hs

def isLUB_csSup (ne : s.Nonempty) (H : BoundedAbove s) : IsLUB s (sSup s) :=
  ⟨fun _ => le_csSup H, fun _ => csSup_le ne⟩

def isLUB_ciSup [Nonempty ι] {f : ι → α} (H : BoundedAbove (range f)) :
    IsLUB (range f) (iSup f) :=
  isLUB_csSup (nonempty_range f) H

def isLUB_ciSup_set {f : β → α} {s : Set β} (H : BoundedAbove (s.image f)) (Hne : s.Nonempty) :
    IsLUB (s.image f) (iSup fun i : s => f i) := by
  rw [← sSup_image']
  exact isLUB_csSup (nonempty_image Hne _) H

def isGLB_csInf (ne : s.Nonempty) (H : BoundedBelow s) : IsGLB s (sInf s) :=
  isLUB_csSup (α := Opposite α) ne H

def isGLB_ciInf [Nonempty ι] {f : ι → α} (H : BoundedBelow (range f)) :
    IsGLB (range f) (iInf f) := isLUB_ciSup (α := Opposite α) H

def isGLB_ciInf_set {f : β → α} {s : Set β} (H : BoundedBelow (s.image f)) (Hne : s.Nonempty) :
    IsGLB (s.image f) (iInf fun i : s => f i) :=
  isLUB_ciSup_set (α := Opposite α) H Hne

def ciSup_le_iff [Nonempty ι] {f : ι → α} {a : α} (hf : BoundedAbove (range f)) :
    iSup f ≤ a ↔ ∀ i, f i ≤ a :=
  (isLUB_le_iff <| isLUB_ciSup hf).trans forall_mem_range

def le_ciInf_iff [Nonempty ι] {f : ι → α} {a : α} (hf : BoundedBelow (range f)) :
    a ≤ iInf f ↔ ∀ i, a ≤ f i := ciSup_le_iff (α := Opposite α) hf

def ciSup_set_le_iff {ι : Type*} {s : Set ι} {f : ι → α} {a : α} (hs : s.Nonempty)
    (hf : BoundedAbove (s.image f)) : iSup (fun i : s => f i) ≤ a ↔ ∀ i ∈ s, f i ≤ a :=
  (isLUB_le_iff <| isLUB_ciSup_set hf hs).trans forall_mem_image

def le_ciInf_set_iff {ι : Type*} {s : Set ι} {f : ι → α} {a : α} (hs : s.Nonempty)
    (hf : BoundedBelow (s.image f)) : (a ≤ iInf fun i : s => f i) ↔ ∀ i ∈ s, a ≤ f i :=
  ciSup_set_le_iff (α := Opposite α) hs hf

def csSup_le_iff (hb : BoundedAbove s) (hs : s.Nonempty) : sSup s ≤ a ↔ ∀ b ∈ s, b ≤ a :=
  isLUB_le_iff (isLUB_csSup hs hb)

def le_csInf_iff (hb : BoundedBelow s) (hs : s.Nonempty) : a ≤ sInf s ↔ ∀ b ∈ s, a ≤ b :=
  le_isGLB_iff (isGLB_csInf hs hb)

def lt_csSup_of_lt (hs : BoundedAbove s) (ha : a ∈ s) (h : b < a) : b < sSup s :=
  lt_of_lt_of_le h (le_csSup hs ha)

def csInf_lt_of_lt : BoundedBelow s → a ∈ s → a < b → sInf s < b :=
  lt_csSup_of_lt (α := Opposite α)

def csSup_singleton (a : α) : sSup {a} = a := by
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

def csInf_singleton (a : α) : sInf {a} = a :=
  csSup_singleton (α := Opposite α) a

def csSup_union (hs : BoundedAbove s) (sne : s.Nonempty) (ht : BoundedAbove t) (tne : t.Nonempty) :
  sSup (s ∪ t) = sSup s ⊔ sSup t := by
  have : sSup s ⊔ sSup t ∈ upperBounds (s ∪ t) := by
    intro x mem
    cases Set.mem_union.mp mem <;> rename_i mem
    apply flip le_trans
    apply le_sup_left
    apply le_csSup
    assumption
    assumption
    apply flip le_trans
    apply le_sup_right
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
  apply le_sup_left
  apply le_csSup
  assumption
  assumption
  apply flip le_trans
  apply le_sup_right
  apply le_csSup
  repeat assumption
  apply sup_le_iff.mpr
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
  sInf (s ∪ t) = sInf s ⊓ sInf t := csSup_union (α := Opposite α) hs sne ht tne

def csSup_insert {a: α} {as: Set α} (ha: BoundedAbove as) (ne: as.Nonempty) : sSup (insert a as) = a ⊔ sSup as := by
  rw [insert_eq, csSup_union, csSup_singleton]
  apply BoundedAbove.singleton
  exact Set.nonempty_singleton _
  assumption
  assumption

def csInf_insert {a: α} {as: Set α} (ha: BoundedBelow as) (ne: as.Nonempty) : sInf (insert a as) = a ⊓ sInf as :=
  csSup_insert (α := Opposite α) ha ne

def csSup_pair (a b : α) : sSup {a, b} = a ⊔ b := by
  rw [csSup_insert, csSup_singleton]
  apply BoundedAbove.singleton
  exact Set.nonempty_singleton _

def csInf_pair (a b : α) : sInf {a, b} = a ⊓ b :=
  csSup_pair (α := Opposite α) a b

def csSup_inter_le (hs: BoundedAbove s) (ht: BoundedAbove t) (ne : (s ∩ t).Nonempty):
  sSup (s ∩ t) ≤ sSup s ⊓ sSup t := by
  have : BoundedAbove (s ∩ t) := by
    obtain ⟨x, hs⟩ := hs
    exists x
    intro y mem
    apply hs
    exact mem.left
  apply le_inf_iff.mpr
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
  sInf s ⊔ sInf t ≤ sInf (s ∩ t) :=
  csSup_inter_le (α := Opposite α) hs ht ne

def ciSup_le [Nonempty ι] {f : ι → α} {c : α} (H : ∀ x, f x ≤ c) : iSup f ≤ c :=
  csSup_le (nonempty_range f) (by rwa [mem_upperBounds, forall_mem_range])

def le_ciInf [Nonempty ι] {f : ι → α} {c : α} (H : ∀ x, c ≤ f x) : c ≤ iInf f :=
  ciSup_le (α := Opposite α) H

def le_ciSup {f : ι → α} (H : BoundedAbove (range f)) (c : ι) : f c ≤ iSup f :=
  le_csSup H Set.mem_range'

def ciInf_le {f : ι → α} (H : BoundedBelow (range f)) (c : ι) : iInf f ≤ f c :=
  csInf_le H Set.mem_range'

def not_mem_of_lt_csInf {x : α} {s : Set α} (h : x < sInf s) (hs : BoundedBelow s) : x ∉ s :=
  fun hx => lt_irrefl (lt_of_lt_of_le h (csInf_le hs hx))

def not_mem_of_csSup_lt {x : α} {s : Set α} (h : sSup s < x) (hs : BoundedAbove s) : x ∉ s :=
  not_mem_of_lt_csInf (α := Opposite α) h hs

namespace Set

theorem IsGLB.csInf_eq (H : IsGLB s a) (ne : s.Nonempty) : sInf s = a :=
  (isGLB_csInf ne ⟨a, H.1⟩).unique H

def IsLeast.csInf_eq (H : IsLeast s a) : sInf s = a :=
  H.isGLB.csInf_eq H.nonempty

end Set
