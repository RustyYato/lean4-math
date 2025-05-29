import Math.Logic.IsEmpty
import Math.Function.Basic
import Math.Order.Notation
import Math.Relation.Defs

import Math.Data.Set.Defs

namespace Set

instance {α} : HasSSubset (Set α) where
  SSubset a b := a ≠ b ∧ a ⊆ b

def ssub_spec {a b: Set α} (h: a ⊂ b) : ∃x ∈ b, x ∉ a := by
  apply Classical.byContradiction
  intro g
  rw [not_exists] at g
  replace g := fun x => not_and.mp (g x)
  apply h.left
  apply sub_antisymm h.right
  intro x mem
  apply Classical.not_not.mp
  apply g
  assumption

def inter_sInter_sub_sInter_inter (a b: Set (Set α)) : ⋂a ∩ ⋂b ⊆ ⋂(a ∩ b) := by
  intro x mem
  simp [mem_sInter, mem_inter] at *
  obtain ⟨ha, hb⟩ := mem
  intro y ya yb
  apply ha
  assumption

@[simp]
def pair_attach {a b: α} : ({a, b}: Set α).attach = {⟨a, mem_pair.mpr (.inl rfl)⟩, ⟨b, mem_pair.mpr (.inr rfl)⟩} := by
  ext x
  cases x with | mk x mem =>
  simp [mem_pair, mem_attach, mem]
  cases mem_pair.mp mem
  subst x; left; rfl
  subst x; right; rfl

@[simp]
def singleton_attach (a: α) : Set.attach {a} = {⟨a, mem_singleton.mpr rfl⟩ } := by
  ext x
  cases x
  simpa [mem_attach]

noncomputable def piecewise (s: Set α) (f g: α -> β) : α -> β :=
  open scoped Classical in
  fun x => if x ∈ s then f x else g x

def range_piecewise (s: Set α) (f: α -> β) (g: α -> β)  :
  Set.range (s.piecewise f g) = s.image f ∪ sᶜ.image g := by
  ext x
  rw [Set.mem_union, Set.mem_image, Set.mem_image]
  apply Iff.intro
  intro ⟨y, eq⟩
  subst x
  unfold piecewise
  by_cases h:y ∈ s
  left
  refine ⟨_, h, ?_⟩
  rw [if_pos h]
  right
  refine ⟨_, h, ?_⟩
  rw [if_neg h]
  intro h
  unfold piecewise
  rcases h with ⟨y, mem, eq⟩ | ⟨y, mem, eq⟩
  exists y
  dsimp; rw [if_pos mem]; assumption
  exists y
  dsimp; rw [if_neg mem]; assumption

end Set

namespace Function

def InjectiveOn (f: α -> β) (s: Set α) : Prop :=
  ∀⦃x y: α⦄, x ∈ s -> y ∈ s -> f x = f y -> x = y

def InjectiveOn_univ_iff_Injective :
  Function.InjectiveOn f ⊤ ↔ Function.Injective f := by
  apply Iff.intro
  intro h x y
  apply h <;> trivial
  intro h x y _ _
  apply h

def SurjectiveOn (f: α -> β) (s: Set α) (t: Set β) : Prop :=
  ∀{y: β}, y ∈ t -> ∃x ∈ s, f x = y

noncomputable def invFun_on {α : Type u} {β} [Nonempty α] (s: Set α) (f : α → β) : β → α :=
  open scoped Classical in
  fun y => Classical.epsilon (fun x => x ∈ s ∧ f x = y)

def invFun_eq_on {s: Set α} {f: α -> β} (h : ∃a ∈ s, f a = b) :
  have := nonempty_of_exists h
  f (invFun_on s f b) = b := by
  simp only [invFun_on, dif_pos h, Classical.epsilon_spec h]

def invFun_eq'_on {x: α} (hf: InjectiveOn f s) (h: x ∈ s):
    have : Nonempty α := ⟨x⟩
   invFun_on s f (f x) = x := by
  dsimp
  unfold invFun_on
  have : ∃x₀, x₀ ∈ s ∧ f x₀ = f x := ⟨x, h, rfl⟩
  have ⟨mem, eq⟩ := Classical.epsilon_spec this
  apply hf
  assumption
  assumption
  assumption

end Function

instance (priority := 900) [SupSet α] : Nonempty α := ⟨⨆∅⟩
instance (priority := 900) [InfSet α] : Nonempty α := ⟨⨅∅⟩
