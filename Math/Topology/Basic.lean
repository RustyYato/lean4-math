import Math.Data.Set.Basic

class HasTopology (α: Type*) where
  IsOpen: Set α -> Prop

open HasTopology in
class IsTopologicalSpace (α: Type*) [HasTopology α]: Prop where
  univ_open: IsOpen (Set.univ α)
  inter_open: ∀{a b: Set α}, IsOpen a -> IsOpen b -> IsOpen (a ∩ b)
  sUnion_open: ∀{a: Set (Set α)}, (∀x ∈ a, IsOpen x) -> IsOpen (⋃ a)

namespace TopologicalSpace

variable [HasTopology α] [HasTopology β] [IsTopologicalSpace α] [IsTopologicalSpace β]

def IsOpen : Set α -> Prop := HasTopology.IsOpen
def IsClosed (s: Set α) : Prop := IsOpen sᶜ
def IsClopen (s: Set α) : Prop := IsOpen s ∧ IsClosed s
def IsLocallyClosed (s : Set α) : Prop := ∃ (x y : Set α), IsOpen x ∧ IsClosed y ∧ s = x ∩ y
-- the largest open subset of s
def Interior (s : Set α) : Set α :=
  ⋃ Set.mk fun x => IsOpen x ∧ x ⊆ s
-- the smallest closed superset of s
def Closure (s : Set α) : Set α :=
  ⋂ Set.mk fun x => IsClosed x ∧ s ⊆ x
-- the smallest closed superset of s
def Frontier (s : Set α) : Set α :=
  Closure s \ Interior s
def Dense (s: Set α) :=
  ∀x, x ∈ Closure s
def DenseRange {X : Type*} (f : X → α) := Dense (Set.range f)

class IsContinuous (f : α → β) : Prop where
  /-- The preimage of an open set under a continuous function is an open set. Use `IsOpen.preimage`
  instead. -/
  isOpen_preimage : ∀s: Set β, IsOpen s → IsOpen (s.preimage f)

def IsOpen.univ : IsOpen (Set.univ α) := IsTopologicalSpace.univ_open
def IsOpen.inter {a b: Set α} : IsOpen a -> IsOpen b -> IsOpen (a ∩ b) := IsTopologicalSpace.inter_open
def IsOpen.sUnion {a: Set (Set α)} : (∀x ∈ a, IsOpen x) -> IsOpen (⋃a) := IsTopologicalSpace.sUnion_open
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
def Frontier.univ : Frontier (Set.univ α) = ∅ := by
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
def Frontier.empty : Frontier (∅: Set α) = ∅ := by
  apply Set.ext_empty
  intro x mem
  erw [Set.mem_sdiff, Closure.empty, Interior.empty] at mem
  obtain ⟨_, _⟩ := mem
  contradiction

def Dense.univ : Dense (Set.univ α) := by
  intro x
  rw [Closure.univ]
  apply Set.mem_univ

def IsContinuous.id : IsContinuous (@id α) where
  isOpen_preimage s sopen := by
    suffices s.preimage (_root_.id ) = s by
      rw [this]; assumption
    ext x
    apply Iff.trans Set.mem_preimage
    apply Iff.intro
    intro ⟨a', a'_in_s, eq⟩
    cases eq
    assumption
    intro h
    exists x

end TopologicalSpace
