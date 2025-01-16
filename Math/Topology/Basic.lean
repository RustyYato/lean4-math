import Math.Data.Set.Basic

class Topology (α: Type*) where
  IsOpen: Set α -> Prop
  univ_open: IsOpen ⊤
  inter_open: ∀{a b: Set α}, IsOpen a -> IsOpen b -> IsOpen (a ∩ b)
  sUnion_open: ∀{a: Set (Set α)}, (∀x ∈ a, IsOpen x) -> IsOpen (⋃ a)

namespace Topology

variable [Topology α] [Topology β] [Topology γ]

def IsClosed (s: Set α) : Prop := IsOpen sᶜ
def IsClopen (s: Set α) : Prop := IsOpen s ∧ IsClosed s
def IsLocallyClosed (s : Set α) : Prop := ∃ (x y : Set α), IsOpen x ∧ IsClosed y ∧ s = x ∩ y
-- the largest open subset of s
def Interior (s : Set α) : Set α :=
  ⋃ Set.mk fun x => IsOpen x ∧ x ⊆ s
-- the smallest closed superset of s
def Closure (s : Set α) : Set α :=
  ⋂ Set.mk fun x => IsClosed x ∧ s ⊆ x
def Border (s : Set α) : Set α :=
  Closure s \ Interior s
def Dense (s: Set α) :=
  ∀x, x ∈ Closure s
def DenseRange {X : Type*} (f : X → α) := Dense (Set.range f)

def OpenSets : Set (Set α) := Set.mk IsOpen
def ClosedSets : Set (Set α) := Set.mk IsClosed

def IsOpen.inj : Function.Injective (α := Topology α) (fun x => x.IsOpen) := by
  intro a b eq
  dsimp at eq
  cases a; cases b; congr

class IsContinuous (f : α → β) : Prop where
  /-- The preimage of an open set under a continuous function is an open set. Use `IsOpen.preimage`
  instead. -/
  isOpen_preimage : ∀s: Set β, IsOpen s → IsOpen (s.preimage f)

def IsOpen.univ : IsOpen (Set.univ α) := Topology.univ_open
def IsOpen.inter {a b: Set α} : IsOpen a -> IsOpen b -> IsOpen (a ∩ b) := Topology.inter_open
def IsOpen.sUnion {a: Set (Set α)} : (∀x ∈ a, IsOpen x) -> IsOpen (⋃a) := Topology.sUnion_open
def IsOpen.preimage (f: α -> β) [IsContinuous f] : ∀s: Set β, IsOpen s → IsOpen (s.preimage f) := IsContinuous.isOpen_preimage
def IsOpen.preimage' {f: α -> β} (h: IsContinuous f) : ∀s: Set β, IsOpen s → IsOpen (s.preimage f) := IsContinuous.isOpen_preimage

def IsOpen.empty : IsOpen (∅: Set α) := by
  rw [←Set.sUnion_empty]
  apply sUnion; intros; contradiction

def IsClosed.univ : IsClosed (Set.univ α) := by
  unfold IsClosed
  rw [Set.univ_compl]
  exact IsOpen.empty
def IsClosed.empty : IsClosed (∅: Set α) := by
  unfold IsClosed
  rw [Set.empty_compl]
  exact IsOpen.univ

def IsClopen.univ : IsClopen (Set.univ α) := ⟨IsOpen.univ, IsClosed.univ⟩
def IsClopen.empty : IsClopen (∅: Set α) := ⟨IsOpen.empty, IsClosed.empty⟩

def Interior.univ : Interior (Set.univ α) = Set.univ α := by
  apply Set.ext_univ
  intro x
  apply Set.mem_sUnion.mpr
  exists Set.univ α
  apply And.intro
  apply And.intro
  apply IsOpen.univ
  rfl
  apply Set.mem_univ
def Closure.univ : Closure (Set.univ α) = Set.univ α := by
  apply Set.ext_univ
  intro x
  apply Set.mem_sInter.mpr
  intro xs ⟨xs_closed, univ_sub_xs⟩
  cases Set.univ_sub _ univ_sub_xs
  apply Set.mem_univ
def Border.univ : Border (Set.univ α) = ∅ := by
  apply Set.ext_empty
  intro x mem
  erw [Set.mem_sdiff, Closure.univ, Interior.univ] at mem
  obtain ⟨_, _⟩ := mem
  contradiction

def Interior.empty : Interior (∅: Set α) = ∅ := by
  apply Set.ext_empty
  intro x mem
  erw [Set.mem_sUnion] at mem
  obtain ⟨xs, ⟨xs_open, sub_empty⟩, mem⟩ := mem
  apply sub_empty
  assumption
def Closure.empty : Closure (∅: Set α) = ∅ := by
  apply Set.ext_empty
  intro x mem
  erw [Set.mem_sInter] at mem
  have := mem ∅ ⟨IsClosed.empty, Set.sub_refl _⟩
  contradiction
def Border.empty : Border (∅: Set α) = ∅ := by
  apply Set.ext_empty
  intro x mem
  erw [Set.mem_sdiff, Closure.empty, Interior.empty] at mem
  obtain ⟨_, _⟩ := mem
  contradiction

def Dense.univ : Dense (Set.univ α) := by
  intro x
  rw [Closure.univ]
  apply Set.mem_univ

def IsContinuous.const (x: β) : IsContinuous (fun _: α => x) where
  isOpen_preimage s sopen := by
    by_cases h:x ∈ s
    suffices s.preimage (fun _: α => x) = Set.univ α by
      rw [this]
      apply IsOpen.univ
    apply Set.ext_univ
    intro
    assumption
    suffices s.preimage (fun _: α => x) = ∅ by
      rw [this]
      apply IsOpen.empty
    apply Set.ext_empty
    intro
    assumption

def IsContinuous.id : IsContinuous (@id α) where
  isOpen_preimage s sopen := by
    suffices s.preimage (_root_.id ) = s by
      rw [this]; assumption
    ext x
    apply Iff.trans Set.mem_preimage
    apply Iff.intro
    exact _root_.id
    exact _root_.id

def IsContinuous.comp (f: α -> β) (g: β -> γ) [IsContinuous f] [IsContinuous g] : IsContinuous (g ∘ f) where
  isOpen_preimage s sopen := isOpen_preimage (f := f) _ <| isOpen_preimage (f := g) s sopen

inductive Trivial.IsOpen: Set α -> Prop where
| empty : Trivial.IsOpen ∅
| univ : Trivial.IsOpen ⊤

def trivial : Topology α where
  IsOpen := Trivial.IsOpen
  univ_open := .univ
  inter_open := by
    intro a b ha hb
    cases ha <;> cases hb
    all_goals
      simp
      try exact .empty
    exact .univ
  sUnion_open := by
    intro s h
    by_cases g:⊤ ∈ s
    suffices ⋃ s = ⊤ by
      rw [this]
      exact .univ
    apply Set.ext_univ
    intro x
    rw [Set.mem_sUnion]
    exists ⊤
    suffices ⋃ s = ∅ by
      rw [this]
      exact .empty
    apply Set.ext_empty
    intro x mem
    rw [Set.mem_sUnion] at mem
    obtain ⟨y, mem, x_in_y⟩ := mem
    cases h _ mem <;> contradiction

def discrete : Topology α where
  IsOpen _ := True
  univ_open := True.intro
  inter_open _ _ := True.intro
  sUnion_open _ := True.intro

instance : Top (Topology α) where
  top := .trivial
instance : Bot (Topology α) where
  bot := .discrete

end Topology
