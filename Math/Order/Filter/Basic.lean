import Math.Data.Set.Finite
import Math.Function.Basic
import Math.Order.Partial

structure Filter (α: Type*) where
  sets: Set (Set α)
  sets_nonempty: sets.Nonempty
  sets_of_superset {x y} : x ∈ sets → x ⊆ y → y ∈ sets
  inter_sets {x y}: x ∈ sets -> y ∈ sets -> x ∩ y ∈ sets

namespace Filter

instance {α : Type*} : Membership (Set α) (Filter α) :=
  ⟨fun F U => U ∈ F.sets⟩

variable {α: Type*} {f g: Filter α} {s t: Set α}

@[simp]
def mem_univ: Set.univ α ∈ f := by
  have ⟨x, x_in_sets⟩ := f.sets_nonempty
  apply Filter.sets_of_superset
  assumption
  apply Set.sub_univ

instance : Inhabited f.sets where
  default := ⟨Set.univ _, mem_univ⟩

def sets_inj : Function.Injective (Filter.sets (α := α)) := by
  intro x y h
  cases x; cases y
  congr

def mem_sets : ∀x, x ∈ f ↔ x ∈ f.sets := by
  intro x
  rfl

@[ext]
def ext : (∀x, x ∈ f ↔ x ∈ g) -> f = g := by
  intro h
  apply sets_inj
  ext
  apply h

def coext : (∀x, xᶜ ∈ f ↔ xᶜ ∈ g) -> f = g := by
  intro h
  ext x
  have := h (xᶜ)
  rw [Set.compl_compl] at this
  assumption

def mem_of_superset {x y : Set α} (hx : x ∈ f) (hxy : x ⊆ y) : y ∈ f :=
  f.sets_of_superset hx hxy

def inter_mem {x y : Set α} (hx : x ∈ f) (hxy : y ∈ f) : x ∩ y ∈ f :=
  f.inter_sets hx hxy

protected def copy (f : Filter α) (S : Set (Set α)) (hmem : ∀ s, s ∈ S ↔ s ∈ f) : Filter α where
  sets := S
  sets_nonempty := ⟨Set.univ _, (hmem _).mpr (mem_univ )⟩
  sets_of_superset h hsub := (hmem _).2 <| mem_of_superset ((hmem _).1 h) hsub
  inter_sets h₁ h₂ := (hmem _).2 <| inter_mem ((hmem _).1 h₁) ((hmem _).1 h₂)

def copy_eq {S} (hmem : ∀ s, s ∈ S ↔ s ∈ f) : f.copy S hmem = f := Filter.ext hmem
@[simp] def mem_copy {S hmem} : s ∈ f.copy S hmem ↔ s ∈ S := Iff.rfl

@[simp]
theorem inter_mem_iff {s t : Set α} : s ∩ t ∈ f ↔ s ∈ f ∧ t ∈ f := by
  apply Iff.intro
  intro h
  apply And.intro
  apply mem_of_superset
  assumption
  apply Set.inter_sub_left
  apply mem_of_superset
  assumption
  apply Set.inter_sub_right
  intro ⟨_, _⟩
  apply inter_mem <;> assumption

@[simp]
theorem sInter_mem {s : Set (Set α)} (hfin : s.IsFinite) : ⋂ s ∈ f ↔ ∀ x ∈ s, x ∈ f := by
  apply hfin.induction
  case nil =>
    simp [Set.sInter_empty]
    intros
    contradiction
  case cons =>
    intro x xs x_not_in_xs xs_finite ih
    simp [Set.sInter_insert, Set.mem_insert, ih]

theorem exists_mem_subset_iff : (∃ t ∈ f, t ⊆ s) ↔ s ∈ f :=
  ⟨fun ⟨_, ht, ts⟩ => mem_of_superset ht ts, fun hs => ⟨s, hs, Set.sub_refl _⟩⟩

end Filter

namespace Filter

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type*} {ι : Sort x}
variable {α: Type*} {f g: Filter α} {s t: Set α}

section Principal

/-- The principal filter of `s` is the collection of all supersets of `s`. -/
def principal (s : Set α) : Filter α where
  sets := .mk fun x => s ⊆ x
  sets_nonempty := ⟨s, Set.sub_refl _⟩
  sets_of_superset := Set.sub_trans
  inter_sets := by
    intro x y
    simp [←Set.sub_inter]
    apply And.intro

scoped notation "𝓟" => Filter.principal

@[simp] theorem mem_principal {s t : Set α} : s ∈ 𝓟 t ↔ t ⊆ s := Iff.rfl

theorem mem_principal_self (s : Set α) : s ∈ 𝓟 s := Set.sub_refl _

end Principal

section Join

def join (fs : Filter (Filter α)) : Filter α where
  sets := Set.mk fun s => (Set.mk fun t : Filter α => s ∈ t) ∈ fs
  sets_nonempty := by
    obtain ⟨x, x_in_fs⟩ := fs.sets_nonempty
    replace x_in_fs: x ∈ fs := x_in_fs
    refine ⟨Set.univ _, ?_⟩
    rw [Set.mk_mem]
    have : (Set.mk fun t: Filter α => Set.univ α ∈ t) = Set.univ _ := by
      apply Set.ext_univ
      intro f
      apply mem_univ
    rw [this]
    exact mem_univ
  sets_of_superset := by
    simp [Set.mk_mem]
    intro x y mem_fs sub
    apply mem_of_superset
    assumption
    intro f
    simp
    intro hx
    apply mem_of_superset
    assumption
    assumption
  inter_sets := by
    simp [Set.mk_mem]
    intro x y hx hy
    suffices ({ Mem := fun t => x ∈ t ∧ y ∈ t }: Set (Filter _)) = { Mem := fun t => x ∈ t } ∩ { Mem := fun t => y ∈ t } by
      rw [this]
      apply inter_mem
      assumption
      assumption
    ext k
    simp [Set.mem_inter]

@[simp]
theorem mem_join {s : Set α} {f : Filter (Filter α)} : s ∈ join f ↔ (Set.mk fun t => s ∈ t) ∈ f :=
  Iff.rfl

end Join

section Order

instance : LE (Filter α) where
  le a b := ∀x ∈ b, x ∈ a

def le_def : (f ≤ g) = ∀x ∈ g, x ∈ f := rfl

instance : LT (Filter α) where
  lt a b := a ≤ b ∧ ¬b ≤ a

instance : IsPartialOrder (Filter α) where
  lt_iff_le_and_not_le := Iff.refl _
  le_antisymm h₁ h₂ := by
    apply sets_inj
    apply Set.sub_antisymm
    assumption
    assumption
  le_refl _ := Set.sub_refl _
  le_trans h₁ h₂ := Set.sub_trans h₂ h₁

def not_le : ¬f ≤ g ↔ ∃s ∈ g, s ∉ f := by
  simp [le_def, Classical.not_forall]

end Order

section Generate

/-- `GenerateSets g s`: `s` is in the filter closure of `g`. -/
inductive GenerateSets (g : Set (Set α)) : Set α → Prop
  | basic {s : Set α} : s ∈ g → GenerateSets g s
  | univ : GenerateSets g univ
  | superset {s t : Set α} : GenerateSets g s → s ⊆ t → GenerateSets g t
  | inter {s t : Set α} : GenerateSets g s → GenerateSets g t → GenerateSets g (s ∩ t)

/-- `generate g` is the largest filter containing the sets `g`. -/
def generate (g : Set (Set α)) : Filter α where
  sets := Set.mk fun s => GenerateSets g s
  sets_nonempty := ⟨Set.univ _, GenerateSets.univ⟩
  sets_of_superset := GenerateSets.superset
  inter_sets := GenerateSets.inter

def mem_generate_of_mem {s : Set <| Set α} {U : Set α} (h : U ∈ s) :
    U ∈ generate s := GenerateSets.basic h

end Generate



end Filter
