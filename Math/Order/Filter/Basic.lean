import Math.Data.Set.Finite
import Math.Data.Set.Lattice
import Math.Function.Basic
import Math.Order.Lattice.Complete
import Math.Order.GaloisConnection

-- a general filter on an arbitrary order
structure FilterBase (α: Type*) [LE α] [Inf α] extends IsLawfulInf α where
  set: Set α
  nonempty: set.Nonempty
  closed_upward: ∀{x y}, x ∈ set -> x ≤ y -> y ∈ set
  closed_inf: ∀{x y}, x ∈ set -> y ∈ set -> x ⊓ y ∈ set

-- a filter over sets using their usual ordering
abbrev Filter (α: Type*) := FilterBase (Set α)

namespace FilterBase

variable {α : Type*} [LE α] [Inf α]

instance : Membership α (FilterBase α) :=
  ⟨fun F U => U ∈ F.set⟩

instance : LE (FilterBase α) where
  le a b := ∀x ∈ b, x ∈ a

instance : LT (FilterBase α) where
  lt a b := a ≤ b ∧ ¬b ≤ a

instance : IsLawfulLT (FilterBase α) where
  lt_iff_le_and_not_le := Iff.rfl

def top_mem' (top: α) (h: ∀x, x ≤ top) (f: FilterBase α): top ∈ f := by
  have ⟨x, mem⟩ := f.nonempty
  apply FilterBase.closed_upward
  assumption
  apply h

@[simp]
def top_mem [Top α] [IsLawfulTop α] (f: FilterBase α): ⊤ ∈ f := by
  apply top_mem'
  apply le_top

instance [Top α] [IsLawfulTop α] (f: FilterBase α) : Inhabited f.set where
  default := ⟨⊤, top_mem f⟩

def set_inj : Function.Injective (FilterBase.set (α := α)) := by
  intro x y h
  cases x; cases y
  congr

def mem_set {f: FilterBase α} : ∀x, x ∈ f ↔ x ∈ f.set := by
  intro x
  rfl

@[ext]
def ext {f g: FilterBase α} : (∀x, x ∈ f ↔ x ∈ g) -> f = g := by
  intro h
  apply set_inj
  ext
  apply h

protected def copy (f : FilterBase α) (S : Set α) (hmem : ∀ s, s ∈ S ↔ s ∈ f) : FilterBase α := by
  have : S = f.set := Set.ext _ _ hmem
  apply FilterBase.mk f.toIsLawfulInf S
  rw [this]; exact f.nonempty
  rw [this]; exact f.closed_upward
  rw [this]; exact f.closed_inf

def copy_eq {f: FilterBase α} {S} (hmem : ∀ s, s ∈ S ↔ s ∈ f) : f.copy S hmem = f := FilterBase.ext hmem
@[simp] def mem_copy {f: FilterBase α} {S hmem} : s ∈ f.copy S hmem ↔ s ∈ S := Iff.rfl

@[simp]
def closed_inf_iff [IsLawfulInf α] {f: FilterBase α} {s t : α} : s ⊓ t ∈ f ↔ s ∈ f ∧ t ∈ f := by
  apply Iff.intro
  intro h
  apply And.intro
  apply closed_upward
  assumption
  apply inf_le_left
  apply closed_upward
  assumption
  apply inf_le_right
  intro ⟨_, _⟩
  apply closed_inf <;> assumption

def closed_finite_sInf [LT α] [InfSet α] [IsCompleteSemiLatticeInf α]
  (s: Set α) [s.IsFinite] (f: FilterBase α): sInf s ∈ f ↔ s ⊆ f.set := by
  induction s using Set.IsFinite.induction with
  | nil =>
    apply Iff.intro
    intro h
    intro _ _; contradiction
    intro
    apply top_mem'
    intro x
    apply le_sInf_empty
  | cons x s hx sfin ih =>
    rw [sInf_insert, closed_inf_iff, ih]
    apply Iff.intro
    intro ⟨_, g⟩
    intro a h
    cases Set.mem_insert.mp h; subst a
    assumption
    apply g
    assumption
    intro g
    apply And.intro
    apply g
    simp
    apply Set.sub_trans _ g
    intro x
    exact .inr

def exists_mem_le_iff [LT α] [IsPreOrder α] {f: FilterBase α} : (∃ t ∈ f, t ≤ s) ↔ s ∈ f :=
  ⟨fun ⟨_, ht, ts⟩ => closed_upward _ ht ts, fun hs => ⟨s, hs, le_refl _⟩⟩

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type*} {ι : Sort x}
variable {α: Type*} [LE α] [LT α] [Inf α] [IsSemiLatticeInf α] {f g: FilterBase α} {s t: α}

section Principal

/-- The principal filter of `s` is the collection of all supersets of `s`. -/
def principal (s : α) : FilterBase α where
  set := .mk fun x => s ≤ x
  nonempty := ⟨s, le_refl _⟩
  closed_upward := le_trans
  closed_inf := by
    intro x y
    simp [←Set.sub_inter]
    intros
    apply And.intro <;> assumption

scoped notation "𝓟" => FilterBase.principal

@[simp] theorem mem_principal {s t : α} : s ∈ 𝓟 t ↔ t ≤ s := Iff.rfl

theorem mem_principal_self (s : α) : s ∈ 𝓟 s := le_refl _

end Principal

namespace Order

def orderEmbSetOp : FilterBase α ↪o (Set α)ᵒᵖ where
  toFun f := f.set
  inj' := FilterBase.set_inj
  resp_rel := Iff.rfl

instance : IsPartialOrder (FilterBase α) :=
  orderEmbSetOp.inducedIsPartialOrder'

def le_def : (f ≤ g) = ∀x ∈ g, x ∈ f := rfl

def not_le : ¬f ≤ g ↔ ∃s ∈ g, s ∉ f := by
  simp [le_def, Classical.not_forall]

end Order

section Generate

inductive GenerateSets (g : Set α) : α → Prop
  | basic {s : α} : s ∈ g → GenerateSets g s
  | up {s t : α} : GenerateSets g s → s ≤ t → GenerateSets g t
  | inf {s t : α} : GenerateSets g s → GenerateSets g t → GenerateSets g (s ⊓ t)

def generate_of_nonempty (g: Set α) (ne: g.Nonempty) : FilterBase α where
  set := Set.mk (GenerateSets g)
  nonempty := by
    obtain ⟨x, ne⟩ := ne
    exists x
    apply GenerateSets.basic
    assumption
  closed_upward := by
    intro x y hx hxy
    apply GenerateSets.up
    assumption
    assumption
  closed_inf := by
    intro x y hx hy
    apply GenerateSets.inf
    assumption
    assumption

def generate [Top α] [IsLawfulTop α] (g: Set α) : FilterBase α := generate_of_nonempty (insert ⊤ g) Set.nonempty_insert

def generate_eq_generate_nonempty [Top α] [IsLawfulTop α] (s: Set α) (h: s.Nonempty) :
  generate_of_nonempty s h = generate s := by
  apply le_antisymm
  · intro x hx
    induction hx with
    | basic =>
      rename_i hx
      rcases hx with hx | hx
      subst hx
      apply top_mem
      apply GenerateSets.basic
      assumption
    | up =>
      apply GenerateSets.up
      assumption
      assumption
    | inf =>
      apply GenerateSets.inf
      assumption
      assumption
  · intro x hx
    induction hx with
    | basic =>
      rename_i hx
      apply GenerateSets.basic
      simp [hx]
    | up =>
      apply GenerateSets.up
      assumption
      assumption
    | inf =>
      apply GenerateSets.inf
      assumption
      assumption

def mem_generate_of_mem {s : Set α} {x : α} (h : x ∈ s) {h': s.Nonempty} :
  x ∈ generate_of_nonempty s h' := GenerateSets.basic h

def le_generate_iff {s : Set α} {f : FilterBase α} {ne: s.Nonempty} : f ≤ generate_of_nonempty s ne ↔ s ⊆ f.set := by
  apply Iff.intro
  intro h x mem
  apply h
  apply GenerateSets.basic
  assumption
  intro h x mem
  induction mem with
  | basic =>
    apply h
    assumption
  | up =>
    apply f.closed_upward
    assumption
    assumption
  | inf =>
    apply f.closed_inf
    assumption
    assumption

def le_generate_iff' [Top α] [IsLawfulTop α] {s : Set α} {f : FilterBase α} : f ≤ generate s ↔ s ⊆ f.set := by
  rw [generate, le_generate_iff]
  apply Iff.intro
  intro h x hx
  apply h
  simp [hx]
  intro h x hx
  simp at hx
  cases hx
  subst x
  apply top_mem
  apply h
  assumption

def mem_generate_iff [InfSet α] [IsCompleteSemiLatticeInf α] {s : Set α} {ne: s.Nonempty} {x: α} : x ∈ generate_of_nonempty s ne ↔ ∃ t ⊆ s, Set.IsFinite t ∧ sInf t ≤ x := by
  apply Iff.intro
  intro mem
  induction mem with
  | basic =>
    rename_i s' _
    exists {s'}
    refine ⟨?_, ?_, ?_⟩
    rwa [Set.singleton_sub]
    infer_instance
    rw [sInf_singleton]
  | up _ h ih =>
    obtain ⟨t, sub, tfin, le⟩ := ih
    refine ⟨t, ?_, tfin, le_trans le ?_⟩
    assumption
    assumption
  | inf _ _ ih₀ ih₁ =>
    obtain ⟨s, ssub, sfin, sle⟩ := ih₀
    obtain ⟨t, tsub, tfin, tle⟩ := ih₁
    refine ⟨s ∪ t, ?_, ?_, ?_⟩
    rw [←Set.union_sub]
    apply And.intro <;> assumption
    infer_instance
    rw [sInf_union]
    apply inf_le_inf
    assumption
    assumption
  intro ⟨t, sub, fin, le⟩
  apply closed_upward _ _ le
  show sInf t ∈ generate_of_nonempty s ne
  apply (closed_finite_sInf _ _).mpr
  intro x mem
  apply GenerateSets.basic
  apply sub
  assumption

@[simp]
def generate_singleton (a: Set α) : generate_of_nonempty {a} (Set.nonempty_singleton _) = 𝓟 a := by
  apply le_antisymm
  intro x mem
  rw [mem_principal] at mem
  rw [mem_generate_iff]
  refine ⟨{a}, Set.sub_refl _, ?_, ?_⟩
  infer_instance
  rw [sInf_singleton]
  assumption
  intro x mem
  rw [mem_generate_iff] at mem
  obtain ⟨t, t_sub, t_fin, le⟩ := mem
  rw [mem_principal]
  apply le_trans _ le
  apply le_sInf
  intro x mem
  cases t_sub _ mem
  rfl

end Generate

def join [Top α] [IsLawfulTop α] (fs : FilterBase (Set (FilterBase α))) : FilterBase α where
  set := Set.mk fun s => (Set.mk fun t : FilterBase α => s ∈ t) ∈ fs
  nonempty := by
    obtain ⟨x, x_in_fs⟩ := fs.nonempty
    replace x_in_fs: x ∈ fs := x_in_fs
    refine ⟨⊤, ?_⟩
    rw [Set.mk_mem]
    have : (Set.mk fun t: FilterBase α => ⊤ ∈ t) = ⊤ := by
      apply Set.ext_univ
      intro f
      apply top_mem
    rw [this]
    apply top_mem
  closed_upward := by
    simp [Set.mk_mem]
    intro x y mem_fs sub
    apply closed_upward
    assumption
    intro f
    simp
    intro hx
    apply closed_upward
    assumption
    assumption
  closed_inf := by
    simp [Set.mk_mem]
    intro x y hx hy
    suffices ({ Mem := fun t => x ∈ t ∧ y ∈ t }: Set (FilterBase _)) = { Mem := fun t => x ∈ t } ∩ { Mem := fun t => y ∈ t } by
      rw [this]
      apply closed_inf
      assumption
      assumption
    ext k
    simp [Set.mem_inter]

@[simp]
def mem_join [Top α] [IsLawfulTop α] {s : α} {f : FilterBase (Set (FilterBase α))} : s ∈ join f ↔ (Set.mk fun t => s ∈ t) ∈ f :=
  Iff.rfl

instance [Top α] [IsLawfulTop α] : Top (FilterBase α) where
  top := {
    set := {⊤}
    nonempty := ⟨⊤, Set.mem_singleton.mp rfl⟩
    closed_upward := by
      intro x y eq h
      subst x
      apply le_antisymm
      apply le_top
      assumption
    closed_inf := by
      intro x y _ _; subst x; subst y
      simp
  }

instance [h: Nonempty α] : Bot (FilterBase α) where
  bot := {
    set := ⊤
    nonempty :=
      have ⟨x⟩ := h
      ⟨x, Set.mem_univ _⟩
    closed_upward := by
      intros
      apply Set.mem_univ
    closed_inf := by
      intros
      apply Set.mem_univ
  }

instance [Top α] [IsLawfulTop α] : SupSet (FilterBase α) where
  sSup := join ∘ 𝓟

instance [Top α] [IsLawfulTop α] : Inf (FilterBase α) where
  inf a b := generate (Set.mk fun s => ∃f₀ f₁: α, f₀ ∈ a ∧ f₁ ∈ b ∧ s = f₀ ⊓ f₁)

protected def mkOfClosure [Top α] [IsLawfulTop α] (s : Set α) (hs : (generate s).set = s) : FilterBase α where
  set := s
  nonempty := hs ▸ nonempty _
  closed_inf := hs ▸ closed_inf _
  closed_upward := hs ▸ closed_upward _

def giGenerate [Top α] [IsLawfulTop α] [InfSet α] [IsCompleteSemiLatticeInf α] :
  GaloisInsertion (α := Set α) (β := Opposite (FilterBase α)) FilterBase.generate FilterBase.set where
  choice s hs := FilterBase.mkOfClosure s (le_antisymm hs <| le_generate_iff.1 <| by
    rw [generate_eq_generate_nonempty])
  choice_eq s _ := by
    dsimp
    apply ext
    intro x
    unfold FilterBase.mkOfClosure
    rw [mem_set]
    dsimp
    apply Iff.intro
    intro hx
    apply GenerateSets.basic
    simp [hx]
    revert x
    assumption
    intro s hs
    exists ⊤
    apply hs
    apply top_mem
  gc _ _ := le_generate_iff'
  le_l_u _ _ h := GenerateSets.basic (Set.mem_insert.mpr (.inr h))

instance instCompleteLattice [Top α] [IsLawfulTop α] [InfSet α] [IsCompleteSemiLatticeInf α] : CompleteLattice (FilterBase α) := {
    (giGenerate (α := α)).liftCompleteLattice.opposite with
    top := ⊤
    inf := (· ⊓ ·)
    sSup := join ∘ 𝓟
    inf_le_left := by
      intro f g x mem
      apply FilterBase.GenerateSets.basic
      rw [Set.mem_insert]; right
      refine ⟨x, ⊤, ?_, ?_, ?_⟩
      assumption
      repeat simp
    inf_le_right := by
      intro f g x mem
      apply FilterBase.GenerateSets.basic
      rw [Set.mem_insert]; right
      refine ⟨⊤, x, ?_, ?_, ?_⟩
      simp
      assumption
      simp
    le_inf := by
      intro a b k ka kb x mem
      induction mem with
      | up =>
        apply closed_upward
        assumption
        assumption
      | inf =>
        apply closed_inf
        assumption
        assumption
      | basic h =>
        cases Set.mem_insert.mp h <;> rename_i h
        subst h; apply top_mem
        obtain ⟨f₀, f₁, f₀_in_a, f₁_in_b, eq⟩ := h
        subst eq; clear h
        apply closed_inf
        apply ka; assumption
        apply kb; assumption
    le_sSup := by
      intro fs f hf x hx
      apply hx
      assumption
    sSup_le := by
      intro f fs ih x mem g hg
      apply ih
      assumption
      assumption
    le_top := by
      intro x a mem; subst a
      apply top_mem
  }

-- a shortcut instance
instance (priority := 5000) : IsCompleteLattice (Filter α) := inferInstance

class NeBot (f: FilterBase α) [Nonempty α] where
  ne : f ≠ ⊥

def not_neBot [Nonempty α] : ¬NeBot f ↔ f = ⊥ := by
  apply Iff.intro
  intro h
  apply Classical.byContradiction
  intro g
  exact h ⟨g⟩
  intro h g
  exact g.ne h

def neBot_of_le [Top α] [IsLawfulTop α] [InfSet α] [IsCompleteSemiLatticeInf α] {f g : FilterBase α} [hf : NeBot f] (hg : f ≤ g) : NeBot g where
  ne := by
    rintro rfl
    apply hf.ne
    apply le_antisymm
    assumption
    apply bot_le

def bot_mem_iff_bot (f: Filter α) : ⊥ ∈ f ↔ f = ⊥ := by
  apply Iff.intro
  intro h
  ext x
  apply Iff.intro
  intro; trivial
  intro
  apply closed_upward
  assumption
  apply bot_le
  rintro rfl
  trivial

end FilterBase

namespace Filter

section Basic

open FilterBase

def univ_mem (f: Filter α) : ⊤ ∈ f := FilterBase.top_mem f

def map (f: α -> β) (F: Filter α) : Filter β where
  set := F.set.preimage (Set.preimage · f)
  nonempty := by
    exists ⊤
    simp [Set.mem_preimage]
    apply univ_mem
  closed_upward := by
    intro a b ha hb
    apply F.closed_upward
    assumption
    dsimp
    intro x hx
    apply hb
    assumption
  closed_inf := F.closed_inf

@[simp]
def map_eq_bot_iff : map m f = ⊥ ↔ f = ⊥ := by
  apply flip Iff.intro
  rintro rfl
  rfl
  intro h
  rename_i α β
  suffices ∅ ∈ f by
    ext x
    apply flip Iff.intro
    intro g
    apply f.closed_upward
    assumption
    apply bot_le
    intro
    trivial
  have : ∅ ∈ map m f := by rw [h]; trivial
  assumption

def map_neBot_iff (f : α → β) {F : Filter α} : NeBot (map f F) ↔ NeBot F := by
  apply Iff.intro
  intro h
  refine ⟨?_⟩
  rintro rfl
  apply h.ne
  rfl
  intro h
  refine ⟨?_⟩
  intro g
  rw [map_eq_bot_iff] at g
  exact h.ne g

instance [NeBot F] : NeBot (map f F) := (map_neBot_iff _).mpr inferInstance

end Basic

section Limit

def Eventually (P: α -> Prop) (f: Filter α) : Prop := Set.mk P ∈ f
def Frequently (P: α -> Prop) (f: Filter α) : Prop := ¬f.Eventually fun x => ¬P x

def TendsTo (f : α -> β) (l₁ : Filter α) (l₂ : Filter β) :=
  l₁.map f ≤ l₂

def tendsto_def {f : α → β} {l₁ : Filter α} {l₂ : Filter β} :
  TendsTo f l₁ l₂ ↔ ∀ s ∈ l₂, s.preimage f ∈ l₁ := Iff.rfl

def TendsTo.eventually {f: α -> β} (h: TendsTo f l₁ l₂) : l₂.Eventually P -> l₁.Eventually (P ∘ f) := h _

@[simp]
def TendsTo.bot {f : α → β} {l : Filter β} : TendsTo f ⊥ l := bot_le _

@[simp]
def TendsTo.top {f : α → β} {l : Filter α} : TendsTo f l ⊤ := le_top _

@[simp]
theorem tendsto_id {x : Filter α} : TendsTo id x x := le_refl x

end Limit

/-- The tail of a sequence is the set of all values that occur after N -/
def tail (seq: ℕ -> α) (N: ℕ) : Set α := Set.image (Set.Ici N) seq

def of_seq (seq: ℕ -> α) : Filter α where
  set := Set.mk fun A => ∃N, tail seq N ⊆ A
  nonempty := ⟨tail seq 0, 0, Set.sub_refl _⟩
  closed_inf := by
    intro x y ⟨n, hx⟩ ⟨m, hy⟩
    exists max n m
    intro i h
    obtain ⟨k, nm_le_k, rfl⟩ := h
    apply And.intro
    apply hx
    apply Set.mem_image.mpr
    refine ⟨_, ?_, rfl⟩
    apply Nat.le_trans _ nm_le_k
    apply Nat.le_max_left
    apply hy
    apply Set.mem_image.mpr
    refine ⟨_, ?_, rfl⟩
    apply Nat.le_trans _ nm_le_k
    apply Nat.le_max_right
  closed_upward := by
    intro x y hx hy
    obtain ⟨n, h⟩ := hx
    exists n
    apply Set.sub_trans _ hy
    assumption

end Filter
