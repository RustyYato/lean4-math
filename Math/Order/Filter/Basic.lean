import Math.Data.Set.Finite
import Math.Function.Basic
import Math.Order.Partial
import Math.Order.Lattice.Complete

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
def univ_mem: ⊤ ∈ f := by
  have ⟨x, x_in_sets⟩ := f.sets_nonempty
  apply Filter.sets_of_superset
  assumption
  apply Set.sub_univ

instance : Inhabited f.sets where
  default := ⟨⊤, univ_mem⟩

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
  sets_nonempty := ⟨⊤, (hmem _).mpr (univ_mem )⟩
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
    refine ⟨⊤, ?_⟩
    rw [Set.mk_mem]
    have : (Set.mk fun t: Filter α => ⊤ ∈ t) = ⊤ := by
      apply Set.ext_univ
      intro f
      apply univ_mem
    rw [this]
    exact univ_mem
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
  | univ : GenerateSets g (⊤)
  | superset {s t : Set α} : GenerateSets g s → s ⊆ t → GenerateSets g t
  | inter {s t : Set α} : GenerateSets g s → GenerateSets g t → GenerateSets g (s ∩ t)

/-- `generate g` is the largest filter containing the sets `g`. -/
def generate (g : Set (Set α)) : Filter α where
  sets := Set.mk (GenerateSets g)
  sets_nonempty := ⟨⊤, GenerateSets.univ⟩
  sets_of_superset := GenerateSets.superset
  inter_sets := GenerateSets.inter

def mem_generate_of_mem {s : Set (Set α)} {x : Set α} (h : x ∈ s) :
    x ∈ generate s := GenerateSets.basic h

theorem le_generate_iff {s : Set (Set α)} {f : Filter α} : f ≤ generate s ↔ s ⊆ f.sets := by
  apply Iff.intro
  intro sub
  intro s' s'_mem_s
  apply sub
  apply mem_generate_of_mem
  assumption
  intro sub s' mem
  induction mem with
  | basic =>
    apply sub
    assumption
  | univ => apply univ_mem
  | superset =>
    apply mem_of_superset
    assumption
    assumption
  | inter =>
    apply inter_mem
    assumption
    assumption

theorem mem_generate_iff {s : Set (Set α)} {x : Set α} : x ∈ generate s ↔ ∃ t ⊆ s, Set.IsFinite t ∧ ⋂ t ⊆ x := by
  apply Iff.intro
  · intro mem
    induction mem with
    | @basic s' mem =>
      exists {s'}
      apply And.intro
      intro x mem
      cases Set.mem_singleton.mp mem
      assumption
      apply And.intro
      infer_instance
      simp
    | univ =>
      exists ∅
      simp
      infer_instance
    | superset _ sub ih  =>
      obtain ⟨t, t_sub_s, tfin, sinter_sub⟩ := ih
      exists t
      simp [Set.sub_trans _ sub, tfin, sinter_sub, t_sub_s]
    | inter _ _ ih₀ ih₁ =>
      obtain ⟨t₀, t₀_sub_s, t₀_fin, sinter_t₀⟩ := ih₀
      obtain ⟨t₁, t₁_sub_s, t₁_fin, sinter_t₁⟩ := ih₁
      exists t₀ ∪ t₁
      apply And.intro
      apply (Set.union_sub _ _ _).mp
      apply And.intro <;> assumption
      apply And.intro
      infer_instance
      rw [Set.sInter_union]
      apply Set.inter_sub_inter
      assumption
      assumption
  · intro ⟨t, t_sub_s, tfin, sinter_sub_x⟩
    apply mem_of_superset
    apply (sInter_mem tfin).mpr
    intro y y_in_t
    apply GenerateSets.basic
    apply t_sub_s
    assumption
    assumption

@[simp]
def generate_singleton (s : Set α) : generate {s} = 𝓟 s := by
  apply le_antisymm
  intro _ ht
  apply mem_of_superset
  apply mem_generate_of_mem
  apply Set.mem_singleton.mpr rfl
  exact ht
  apply le_generate_iff.mpr
  simp [Set.singleton_sub, principal]

end Generate

section Lattice

-- def inf (a b: Filter α) : Filter α where
--   sets := Set.mk fun x => ∃a' ∈ a, ∃b' ∈ b, x = a' ∩ b'
--   sets_nonempty := by
--     have ⟨a', a'_mem⟩  := a.sets_nonempty
--     have ⟨b', b'_mem⟩  := b.sets_nonempty
--     refine ⟨a' ∩ b', ?_⟩
--     exists a'
--     apply And.intro a'_mem
--     exists b'
--   sets_of_superset := by
--     intro x y memx xsuby
--     obtain ⟨a', a'_in_a, b', b'_in_b, x_eq⟩  := memx
--     subst x
--     exists a' ∪ y
--     apply And.intro
--     apply mem_of_superset
--     assumption
--     apply Set.sub_union_left
--     exists b' ∪ y
--     apply And.intro
--     apply mem_of_superset
--     assumption
--     apply Set.sub_union_left
--     rw [←Set.union_inter_right]
--     apply Set.sub_antisymm
--     apply Set.sub_union_right
--     apply (Set.union_sub _ _ _).mp
--     apply And.intro
--     assumption
--     rfl
--   inter_sets := by
--     intro x y hx hy
--     obtain ⟨xa, xa_in_a, xb, xb_in_b, xeq⟩ := hx
--     obtain ⟨ya, ya_in_a, yb, yb_in_b, yeq⟩ := hy
--     subst x; subst y
--     exists xa ∩ ya
--     apply And.intro
--     apply inter_mem
--     assumption
--     assumption
--     exists xb ∩ yb
--     apply And.intro
--     apply inter_mem
--     assumption
--     assumption
--     ac_rfl

def sInf (fs: Set (Filter α)) :=
  Filter.generate (Set.mk fun s => ∃f: fs -> Set α, (∀x, (f x) ∈ x.val) ∧ s = ⋂(fs.attach.image f))

-- def sInf (fs: Set (Filter α)) : Filter α where
--   sets := Set.mk fun s => ∃f: fs -> Set α, ∃g: ∀x, (f x) ∈ x.val, s = ⋂(fs.attach.image f)
--   sets_nonempty := by
--     by_cases hfs:fs.Nonempty
--     exists ⊤
--     simp
--     exists (fun _ => ⊤)
--     apply And.intro
--     intro
--     apply univ_mem
--     rw [Set.image_const_of_nonempty]
--     simp
--     rw [Set.nonempty_attach]
--     assumption
--     cases Set.not_nonempty _ hfs
--     exists ⊤
--     refine ⟨fun _ => (⊤), ?_, ?_⟩
--     intro h
--     have := Set.not_mem_empty h.property
--     contradiction
--     simp
--   sets_of_superset := by
--     intro x y hx x_sub_y

--     obtain ⟨f, g, _⟩ := hx; subst x
--     refine ⟨?_, ?_, ?_⟩
--     intro elem
--     let x := f elem
--     have := g elem





--     -- intro x y hx hy
--     -- have hx := Set.mem_sInter.mp hx
--     -- apply Set.mem_sInter.mpr
--     -- intro z hz
--     -- have ⟨f, f_in_a, eq⟩ := Set.mem_image.mp hz
--     -- subst eq
--     -- apply mem_of_superset
--     -- apply hx
--     -- assumption
--     -- assumption
--   inter_sets := by
--     sorry
--     -- intro x y hx hy
--     -- have hx := Set.mem_sInter.mp hx
--     -- have hy := Set.mem_sInter.mp hy
--     -- apply Set.mem_sInter.mpr
--     -- intro z hz
--     -- have ⟨f, f_in_a, eq⟩ := Set.mem_image.mp hz
--     -- subst eq
--     -- apply inter_mem
--     -- apply hx; assumption
--     -- apply hy; assumption

instance : SupSet (Filter α) where
  sSup := join ∘ 𝓟

instance : InfSet (Filter α) := ⟨sInf⟩

instance : Inf (Filter α) where
  inf a b := sInf {a, b}
instance : Sup (Filter α) where
  sup a b := sSup {a, b}

def mem_inf_iff {a b: Filter α} : ∀{x}, x ∈ a ⊓ b ↔ ∃xa ∈ a, ∃xb ∈ b, x = xa ∩ xb := by
  intro x
  show _  ∈ sInf _ ↔ _
  rw [sInf]
  apply Iff.intro
  · intro hx
    induction hx with
    | basic hx =>
      rename_i s
      obtain ⟨f, spec, eq⟩ := hx
      rw [Set.pair_attach, Set.pair_image, Set.sInter_pair] at eq
      subst s
      refine ⟨f ⟨a, ?_⟩, ?_, f ⟨b, ?_⟩, ?_, rfl⟩
      simp
      apply spec ⟨_, _⟩
      simp
      apply spec ⟨_, _⟩
    | univ => refine ⟨⊤, ?_, ⊤, ?_⟩ <;> simp
    | superset mem sub ih =>
      rename_i s t
      obtain ⟨xa, xa_mem, xb, xb_mem, eq⟩ := ih
      subst eq
      refine ⟨xa ∪ t, ?_, xb ∪ t, ?_, ?_⟩
      apply mem_of_superset
      assumption
      apply Set.sub_union_left
      apply mem_of_superset
      assumption
      apply Set.sub_union_left
      rw [←Set.union_inter_right, Set.union_of_sub_left]
      assumption
    | inter mem₀ mem₁ ih₀ ih₁ =>
      obtain ⟨xa₀, xa₀_mem, xb₀, xb₀_mem, eq⟩ := ih₀; subst eq
      obtain ⟨xa₁, xa₁_mem, xb₁, xb₁_mem, eq⟩ := ih₁; subst eq
      refine ⟨xa₀ ∩ xa₁, ?_, xb₀ ∩ xb₁, ?_, ?_⟩
      apply inter_mem <;> assumption
      apply inter_mem <;> assumption
      ac_rfl
  · intro ⟨xa, hxa, xb, hxb, eq⟩
    subst eq
    if h:a = b then
      subst b
      have : ({a, a}: Set _) = {a} := by ext; simp
      rw [show  ({a, a}: Set _) = {a} from by ext; simp]
      apply GenerateSets.basic
      refine ⟨fun _ => xa ∩ xb, ?_⟩
      apply And.intro
      intro ⟨x, hx⟩; subst x
      dsimp
      apply inter_mem
      assumption
      assumption
      simp
    else
      apply GenerateSets.basic
      refine ⟨?_, ?_⟩
      intro ⟨x, _⟩
      if x = a then
        exact xa
      else
        exact xb
      apply And.intro
      dsimp
      intro ⟨x, hx⟩
      rw [Set.mem_pair] at hx
      dsimp
      split
      subst x
      assumption
      cases hx; contradiction; subst x
      assumption
      simp
      rw [if_neg]
      apply Ne.symm; assumption

def mem_inf_left {a b: Filter α} {s: Set α} : s ∈ a -> s ∈ a ⊓ b
| h => mem_inf_iff.mpr ⟨s, h, _, univ_mem, by simp⟩

def mem_inf_right {a b: Filter α} {s: Set α} : s ∈ b -> s ∈ a ⊓ b
| h => mem_inf_iff.mpr ⟨_, univ_mem, s, h, by simp⟩

def mem_inf_of_inter {a b: Filter α} {s t: Set α} : s ∈ a -> t ∈ b -> s ∩ t ∈ a ⊓ b
| h, g => mem_inf_iff.mpr ⟨_, h, _, g, by simp⟩

def top α: Filter α where
  sets := {⊤}
  sets_nonempty := ⟨_, Set.mem_singleton.mpr rfl⟩
  inter_sets := by
    intro x y hx hy
    cases Set.mem_singleton.mp hx
    simp [hy]
  sets_of_superset := by
    intro x y hx hy
    cases Set.mem_singleton.mp hx
    cases Set.univ_sub _ hy
    simp [Set.mem_singleton]

def bot α: Filter α where
  sets := ⊤
  sets_nonempty := ⟨_, Set.mem_univ (⊤)⟩
  inter_sets := by
    intro x y hx hy
    apply Set.mem_univ
  sets_of_superset := by
    intro x y hx hy
    apply Set.mem_univ

instance : Top (Filter α) := ⟨top _⟩
instance : Bot (Filter α) := ⟨bot _⟩

def mem_top (x: Set α) : x ∈ (⊤: Filter α) ↔ x = ⊤ := Set.mem_singleton

-- instance : IsCompleteLattice (Filter α) where

end Lattice

end Filter
