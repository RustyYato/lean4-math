import Math.Data.Set.Basic

class Topology (α: Type*) where
  IsOpen: Set α -> Prop
  univ_open: IsOpen ⊤
  inter_open: ∀{a b: Set α}, IsOpen a -> IsOpen b -> IsOpen (a ∩ b)
  sUnion_open: ∀{a: Set (Set α)}, (∀x ∈ a, IsOpen x) -> IsOpen (⋃ a)

namespace Topology

variable [Topology α] [Topology β] [Topology γ]

scoped notation "IsOpen[" T "]" => @IsOpen _ T

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

def OpenSets (t: Topology α) : Set (Set α) := Set.mk IsOpen
def ClosedSets (t: Topology α) : Set (Set α) := Set.mk IsClosed

def IsOpen.inj : Function.Injective (α := Topology α) (fun x => x.IsOpen) := by
  intro a b eq
  dsimp at eq
  cases a; cases b; congr

def OpenSets.inj : Function.Injective (α := Topology α) OpenSets := by
  intro a b eq
  apply IsOpen.inj
  dsimp
  apply Set.mk.inj
  assumption

@[ext]
def ext (a b: Topology α) : (∀x, IsOpen[a] x ↔ IsOpen[b] x) -> a = b := by
  intro h
  apply IsOpen.inj
  ext
  apply h

class IsContinuous (f : α → β) : Prop where
  /-- The preimage of an open set under a continuous function is an open set. Use `IsOpen.preimage`
  instead. -/
  isOpen_preimage : ∀s: Set β, IsOpen s → IsOpen (s.preimage f)

abbrev IsContinuous' (Tα) (Tβ) (f: α -> β) := @IsContinuous α β Tα Tβ f

abbrev IsContinuous'.mk (Tα: Topology α) (Tβ: Topology β) (f: α -> β) :
  (∀s: Set β, IsOpen s → IsOpen (s.preimage f)) ->
  IsContinuous' Tα Tβ f := (⟨·⟩)

def IsOpen.univ {top: Topology α} : IsOpen[top] (Set.univ α) := Topology.univ_open
def IsOpen.inter {top: Topology α} {a b: Set α} : IsOpen[top] a -> IsOpen[top] b -> IsOpen[top] (a ∩ b) := Topology.inter_open
def IsOpen.sUnion {top: Topology α} {a: Set (Set α)} : (∀x ∈ a, IsOpen[top] x) -> IsOpen[top] (⋃a) := Topology.sUnion_open
def IsOpen.union {top: Topology α} {a b: Set α} : IsOpen[top] a -> IsOpen[top] b -> IsOpen[top] (a ∪ b) := by
  intro ha hb
  rw [←Set.sUnion_pair]
  apply IsOpen.sUnion
  intro x hx
  simp at hx
  rcases hx with rfl | rfl <;> assumption
def IsOpen.preimage (f: α -> β) [IsContinuous f] : ∀s: Set β, IsOpen s → IsOpen (s.preimage f) := IsContinuous.isOpen_preimage
def IsOpen.preimage' {f: α -> β} (h: IsContinuous f) : ∀s: Set β, IsOpen s → IsOpen (s.preimage f) := IsContinuous.isOpen_preimage

def IsOpen.Interior (s: Set α) : IsOpen (Interior s) := by
  apply IsOpen.sUnion
  intro x hx
  rw [Set.mk_mem] at hx
  exact hx.left

def interior_sub (s: Set α) : Interior s ≤ s := by
  intro x hx
  erw [Set.mem_sUnion] at hx
  obtain ⟨_, ⟨_, g⟩, _⟩ := hx
  apply g
  assumption

def IsOpen.empty : IsOpen (∅: Set α) := by
  rw [←Set.sUnion_empty]
  apply sUnion; intros; contradiction

def IsClosed.univ : IsClosed (⊤: Set α) := by
  unfold IsClosed
  rw [Set.univ_compl]
  exact IsOpen.empty
def IsClosed.empty : IsClosed (∅: Set α) := by
  unfold IsClosed
  rw [Set.empty_compl]
  exact IsOpen.univ
def IsClosed.preimage (f: α -> β) [IsContinuous f] : ∀s: Set β, IsClosed s → IsClosed (s.preimage f) := by
  intro s hs
  exact IsOpen.preimage f sᶜ hs

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

instance IsContinuous.const (x: β) : IsContinuous (fun _: α => x) where
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

instance IsContinuous.id : IsContinuous (@id α) where
  isOpen_preimage s sopen := by
    suffices s.preimage (_root_.id ) = s by
      rw [this]; assumption
    ext x
    apply Iff.trans Set.mem_preimage
    apply Iff.intro
    exact _root_.id
    exact _root_.id

instance IsContinuous.id' : IsContinuous (fun x: α => x) :=
  IsContinuous.id

instance IsContinuous.comp (f: α -> β) (g: β -> γ) [IsContinuous f] [IsContinuous g] : IsContinuous (g ∘ f) where
  isOpen_preimage s sopen := isOpen_preimage (f := f) _ <| isOpen_preimage (f := g) s sopen

def IsContinuous.comp' {f: α -> β} {g: β -> γ} (hf: IsContinuous f) (hg: IsContinuous g) : IsContinuous (g ∘ f) :=
  inferInstance

def Pairwise (P: α -> α -> Prop) : Prop := ∀{a b}, a ≠ b -> P a b

inductive trivial_isopen: Set α -> Prop where
| empty : trivial_isopen ∅
| univ : trivial_isopen ⊤

def trivial : Topology α where
  IsOpen := trivial_isopen
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

inductive Generate.IsOpen (U: Set (Set α)) : Set α -> Prop where
| of : x ∈ U -> IsOpen U x
| univ : IsOpen U ⊤
| inter : IsOpen U a -> IsOpen U b -> IsOpen U (a ∩ b)
| sUnion {s: Set (Set α)} : (∀x ∈ s, IsOpen U x) -> IsOpen U (⋃ s)

-- the smallest Topology where all of the given sets are Open
def generate (U: Set (Set α)) : Topology α where
  IsOpen := Generate.IsOpen U
  univ_open := Generate.IsOpen.univ
  inter_open := Generate.IsOpen.inter
  sUnion_open := Generate.IsOpen.sUnion

def Generate.IsOpen.map (U: Set (Set α)) {tb: Topology β}:
  Generate.IsOpen U s ->
  ∀{f: β -> α},
  (∀x ∈ U, Topology.IsOpen (x.preimage f)) ->
  Topology.IsOpen (s.preimage f) := by
  intro op t h
  induction op with
  | univ => apply Topology.IsOpen.univ
  | inter =>
    rw [Set.preimage_inter]
    apply Topology.IsOpen.inter
    assumption
    assumption
  | sUnion _ ih =>
    rw [Set.preimage_sUnion]
    apply Topology.IsOpen.sUnion
    intro _ ⟨x, h, eq⟩
    subst eq
    exact ih x h
  | of =>
    apply h
    assumption

class Discrete (α: Type*) extends Topology α where
  eq_bot: toTopology = ⊥

class Trivial (α: Type*) extends Topology α where
  eq_top: toTopology = ⊤

instance [Subsingleton α₀] : Topology α₀ := ⊥
instance [Subsingleton α₀] : Discrete α₀ := ⟨rfl⟩
instance [Subsingleton α₀] : Trivial α₀ where
  eq_top := by
    apply Topology.IsOpen.inj
    unfold instOfSubsingleton
    ext x
    have : x = ∅ ∨ x = ⊤ := by
      by_cases h:x.Nonempty
      right
      apply Set.ext_univ
      intro y
      obtain ⟨y', _⟩  := h
      rw [Subsingleton.allEq y y']
      assumption
      left; exact Set.not_nonempty x h
    cases this <;> subst x
    apply Iff.intro
    intro h
    exact @Topology.IsOpen.empty α₀ ⊤
    intro
    exact @Topology.IsOpen.empty α₀ ⊥
    apply Iff.intro
    intro h
    exact @Topology.IsOpen.univ α₀ ⊤
    intro
    exact @Topology.IsOpen.univ α₀ ⊥

instance : Topology Bool := ⊥
instance : Discrete Bool := ⟨rfl⟩

instance : Topology (Fin n) := ⊥
instance : Discrete (Fin n) := ⟨rfl⟩

instance : Topology Nat := ⊥
instance : Discrete Nat := ⟨rfl⟩

instance : Topology Int := ⊥
instance : Discrete Int := ⟨rfl⟩

def induced (f: α -> β) (t: Topology β) : Topology α where
  IsOpen s := ∃ t, IsOpen t ∧ t.preimage f = s
  univ_open := by
    dsimp
    exists ⊤
    apply And.intro IsOpen.univ
    rfl
  inter_open := by
    intro a b ⟨a', a'_open, ha⟩ ⟨b', b'_open, hb⟩
    exists a' ∩ b'
    apply And.intro
    apply IsOpen.inter <;> assumption
    show a'.preimage f ∩ b'.preimage f = _
    congr
  sUnion_open := by
    intro S h
    dsimp at h
    let g := fun x (hx: x ∈ S) => Classical.choose (h x hx)
    exists ⋃S.attach.image fun x => g x.val x.property
    apply And.intro
    apply IsOpen.sUnion
    intro _ ⟨⟨x, mem⟩, mem', eq⟩
    subst eq; clear mem'
    dsimp
    exact (Classical.choose_spec (h x mem)).left
    have := fun x mem => (Classical.choose_spec (h x mem)).right
    rw [Set.preimage_sUnion, Set.image_image]
    show ⋃(S.attach.image fun _ => Set.preimage _ _) = _
    conv => {
      lhs; arg 1; arg 2; intro x
      rw [this x.val x.property]
    }
    rw [Set.attach_image_val]

def coinduced (f: α -> β) (t: Topology α) : Topology β where
  IsOpen s := s.preimage f ∈ t.OpenSets
  univ_open := IsOpen.univ
  inter_open := IsOpen.inter
  sUnion_open := by
    intro s h
    suffices (⋃s).preimage f = ⋃(s.image fun x => x.preimage f) by
      rw [this]
      apply IsOpen.sUnion
      intro x ⟨s', mem, eq⟩
      subst x
      dsimp
      apply h
      assumption
    rw [Set.preimage_sUnion]

instance {P: α -> Prop} [Topology α] : Topology (Subtype P) :=
  Topology.induced Subtype.val inferInstance

instance {P: α -> Prop} [Topology α] : Topology.IsContinuous (Subtype.val (p := P)) where
  isOpen_preimage := by
    intro S Sopen
    exists S

end Topology

def Topology.IsContinuous.bot_dom (f: α -> β) [Tα: Topology.Discrete α] [Tβ: Topology β] : IsContinuous f where
  isOpen_preimage := by
    cases Tα
    rename_i eq_bot
    cases eq_bot
    intro s _
    exact True.intro

def Topology.IsContinuous.top_rng (f: α -> β) [Tα: Topology α] [Tβ: Topology.Trivial β] : IsContinuous f where
  isOpen_preimage := by
    cases Tβ
    rename_i eq_top
    cases eq_top
    intro s o
    cases o
    apply IsOpen.empty
    apply IsOpen.univ
