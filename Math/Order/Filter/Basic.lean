import Math.Data.Set.Finite
import Math.Data.Set.Lattice
import Math.Function.Basic
import Math.Order.Partial
import Math.Order.Lattice.Complete

structure Filter (α: Type*) [LE α] [Inf α] extends IsLawfulInf α where
  set: Set α
  nonempty: set.Nonempty
  closed_upward: ∀{x y}, x ∈ set -> x ≤ y -> y ∈ set
  closed_inf: ∀{x y}, x ∈ set -> y ∈ set -> x ⊓ y ∈ set

namespace Filter

variable {α : Type*} [LE α] [Inf α]

instance : Membership α (Filter α) :=
  ⟨fun F U => U ∈ F.set⟩

instance : LE (Filter α) where
  le a b := ∀x ∈ b, x ∈ a

instance : LT (Filter α) where
  lt a b := a ≤ b ∧ ¬b ≤ a

instance : IsLawfulLT (Filter α) where
  lt_iff_le_and_not_le := Iff.rfl

def top_mem' (top: α) (h: ∀x, x ≤ top) (f: Filter α): top ∈ f := by
  have ⟨x, mem⟩ := f.nonempty
  apply Filter.closed_upward
  assumption
  apply h

@[simp]
def top_mem [Top α] [IsLawfulTop α] (f: Filter α): ⊤ ∈ f := by
  apply top_mem'
  apply le_top

instance [Top α] [IsLawfulTop α] (f: Filter α) : Inhabited f.set where
  default := ⟨⊤, top_mem f⟩

def set_inj : Function.Injective (Filter.set (α := α)) := by
  intro x y h
  cases x; cases y
  congr

def mem_set {f: Filter α} : ∀x, x ∈ f ↔ x ∈ f.set := by
  intro x
  rfl

@[ext]
def ext {f g: Filter α} : (∀x, x ∈ f ↔ x ∈ g) -> f = g := by
  intro h
  apply set_inj
  ext
  apply h

protected def copy (f : Filter α) (S : Set α) (hmem : ∀ s, s ∈ S ↔ s ∈ f) : Filter α := by
  have : S = f.set := Set.ext _ _ hmem
  apply Filter.mk f.toIsLawfulInf S
  rw [this]; exact f.nonempty
  rw [this]; exact f.closed_upward
  rw [this]; exact f.closed_inf

def copy_eq {f: Filter α} {S} (hmem : ∀ s, s ∈ S ↔ s ∈ f) : f.copy S hmem = f := Filter.ext hmem
@[simp] def mem_copy {f: Filter α} {S hmem} : s ∈ f.copy S hmem ↔ s ∈ S := Iff.rfl

@[simp]
def closed_inf_iff [IsLawfulInf α] {f: Filter α} {s t : α} : s ⊓ t ∈ f ↔ s ∈ f ∧ t ∈ f := by
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
  (s: Set α) [s.IsFinite] (f: Filter α): sInf s ∈ f ↔ s ⊆ f.set := by
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

def exists_mem_le_iff [LT α] [IsPreOrder α] {f: Filter α} : (∃ t ∈ f, t ≤ s) ↔ s ∈ f :=
  ⟨fun ⟨_, ht, ts⟩ => closed_upward _ ht ts, fun hs => ⟨s, hs, le_refl _⟩⟩

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type*} {ι : Sort x}
variable {α: Type*} [LE α] [LT α] [Inf α] [IsSemiLatticeInf α] {f g: Filter α} {s t: α}

section Principal

/-- The principal filter of `s` is the collection of all supersets of `s`. -/
def principal (s : α) : Filter α where
  set := .mk fun x => s ≤ x
  nonempty := ⟨s, le_refl _⟩
  closed_upward := le_trans
  closed_inf := by
    intro x y
    simp [←Set.sub_inter]
    intros
    apply And.intro <;> assumption

scoped notation "𝓟" => Filter.principal

@[simp] theorem mem_principal {s t : α} : s ∈ 𝓟 t ↔ t ≤ s := Iff.rfl

theorem mem_principal_self (s : α) : s ∈ 𝓟 s := le_refl _

end Principal

namespace Order

def orderEmbSetOp : Filter α ↪o (Set α)ᵒᵖ where
  toFun f := f.set
  inj := Filter.set_inj
  resp_rel := Iff.rfl

instance : IsPartialOrder (Filter α) :=
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

def generate_of_nonempty (g: Set α) (ne: g.Nonempty) : Filter α where
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

def generate [Top α] [IsLawfulTop α] (g: Set α) : Filter α := generate_of_nonempty (insert ⊤ g) Set.nonempty_insert

def mem_generate_of_mem {s : Set α} {x : α} (h : x ∈ s) {h': s.Nonempty} :
  x ∈ generate_of_nonempty s h' := GenerateSets.basic h

def le_generate_iff {s : Set α} {f : Filter α} {ne: s.Nonempty} : f ≤ generate_of_nonempty s ne ↔ s ⊆ f.set := by
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

def join [Top α] [IsLawfulTop α] (fs : Filter (Set (Filter α))) : Filter α where
  set := Set.mk fun s => (Set.mk fun t : Filter α => s ∈ t) ∈ fs
  nonempty := by
    obtain ⟨x, x_in_fs⟩ := fs.nonempty
    replace x_in_fs: x ∈ fs := x_in_fs
    refine ⟨⊤, ?_⟩
    rw [Set.mk_mem]
    have : (Set.mk fun t: Filter α => ⊤ ∈ t) = ⊤ := by
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
    suffices ({ Mem := fun t => x ∈ t ∧ y ∈ t }: Set (Filter _)) = { Mem := fun t => x ∈ t } ∩ { Mem := fun t => y ∈ t } by
      rw [this]
      apply closed_inf
      assumption
      assumption
    ext k
    simp [Set.mem_inter]

@[simp]
def mem_join [Top α] [IsLawfulTop α] {s : α} {f : Filter (Set (Filter α))} : s ∈ join f ↔ (Set.mk fun t => s ∈ t) ∈ f :=
  Iff.rfl

instance [Top α] [IsLawfulTop α] : Top (Filter α) where
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

instance [h: Nonempty α] : Bot (Filter α) where
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

instance [Top α] [IsLawfulTop α] [InfSet α] : InfSet (Filter α) where
  sInf fs := generate (Set.mk fun s => ∃f: fs -> α, (∀x, (f x) ∈ x.val) ∧ s = iInf f)

instance [Top α] [IsLawfulTop α] : SupSet (Filter α) where
  sSup := join ∘ 𝓟

instance [Top α] [IsLawfulTop α] : Inf (Filter α) where
  inf a b := generate (Set.mk fun s => ∃f₀ f₁: α, f₀ ∈ a ∧ f₁ ∈ b ∧ s = f₀ ⊓ f₁)
instance [Top α] [IsLawfulTop α] : Sup (Filter α) where
  sup a b := sSup {a, b}

instance [Top α] [IsLawfulTop α] [InfSet α] [IsCompleteSemiLatticeInf α] : IsCompleteLattice (Filter α) where
  le_top := by
    intro x a mem; subst a
    apply top_mem
  bot_le := by
    intro x a mem
    trivial
  le_sup_left := by
    intro f g a mem
    apply mem
    simp
  le_sup_right := by
    intro f g a mem
    apply mem
    simp
  inf_le_left := by
    intro f g x mem
    apply Filter.GenerateSets.basic
    rw [Set.mem_insert]; right
    refine ⟨x, ⊤, ?_, ?_, ?_⟩
    assumption
    repeat simp
  inf_le_right := by
    intro f g x mem
    apply Filter.GenerateSets.basic
    rw [Set.mem_insert]; right
    refine ⟨⊤, x, ?_, ?_, ?_⟩
    simp
    assumption
    simp
  sup_le := by
    intro f g k kf kg x mem
    have := kf x mem
    have := kg x mem
    intro i mem
    simp at mem; cases mem <;> subst i
    assumption
    assumption
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
  sInf_le := by
    intro fs f hf x hx
    apply GenerateSets.basic
    simp; right
    refine ⟨?_, ?_, ?_⟩
    sorry
    sorry
    sorry
  le_sInf := sorry


end Filter
