import Math.Order.Filter.Directed
import Math.Data.Set.Order.Interval
import Math.Order.Directed.Finite

open FilterBase

namespace Filter

section

variable {α} [LT α] [LE α]

def atTop := ⨅ a: α, 𝓟 (Set.Ici a)
def atBot := ⨅ a: α, 𝓟 (Set.Iic a)

def mem_atTop (a : α) : (Set.mk fun b => a ≤ b) ∈ @atTop α _ := by
  apply mem_generate_of_mem
  simp [Set.mem_sUnion, Set.mem_range, Set.mem_image]
  right
  refine ⟨_, ⟨_, ⟨a, rfl⟩, rfl⟩, ?_⟩
  apply mem_principal_self
  exists ⊤; simp

def mem_atBot (a : α) : (Set.mk fun b => b ≤ a) ∈ @atBot α _ := by
  apply mem_generate_of_mem
  simp [Set.mem_sUnion, Set.mem_range, Set.mem_image]
  right
  refine ⟨_, ⟨_, ⟨a, rfl⟩, rfl⟩, ?_⟩
  apply mem_principal_self
  exists ⊤; simp

def eventually_ge_atTop (a : α) : Eventually (fun x => a ≤ x) atTop :=
  mem_atTop a

def eventually_le_atBot (a : α) : Eventually (fun x => x ≤ a) atBot :=
  mem_atBot a

instance neBot_atTop [hα: Nonempty α] [IsDirected α (· ≤ ·)] [IsPreOrder α] : NeBot (atTop (α := α)) := by
  apply sInf_neBot_of_directed'
  obtain ⟨a⟩ := hα
  exists 𝓟 (Set.Ici a)
  apply Set.mem_range'
  rintro f₀ ⟨a₀, rfl⟩  f₁ ⟨a₁, rfl⟩
  have ⟨c, h₀, h₁⟩ := isDirected (· ≤ ·) a₀ a₁
  simp at h₀ h₁
  simp
  exists 𝓟 (Set.Ici c)
  apply And.intro
  exists c
  apply And.intro
  iterate 2
    apply principal_le_principal
    intro x hx
    apply le_trans
    assumption
    assumption
  intro ⟨a, eq⟩
  simp at eq
  have : Set.Iio a ∈ (⊥: Filter α) := by trivial
  rw [eq] at this
  rw [mem_principal] at this
  exact lt_irrefl (this a (le_refl _))

instance neBot_atBot [hα: Nonempty α] [IsDirected α (· ≥ ·)] [IsPreOrder α] : NeBot (atBot (α := α)) := by
  apply sInf_neBot_of_directed'
  obtain ⟨a⟩ := hα
  exists 𝓟 (Set.Iic a)
  apply Set.mem_range'
  rintro f₀ ⟨a₀, rfl⟩  f₁ ⟨a₁, rfl⟩
  have ⟨c, h₀, h₁⟩ := isDirected (· ≥ ·) a₀ a₁
  simp at h₀ h₁
  simp
  exists 𝓟 (Set.Iic c)
  apply And.intro
  exists c
  apply And.intro
  iterate 2
    apply principal_le_principal
    intro x hx
    apply le_trans
    assumption
    assumption
  intro ⟨a, eq⟩
  simp at eq
  have : Set.Iio a ∈ (⊥: Filter α) := by trivial
  rw [eq] at this
  rw [mem_principal] at this
  exact lt_irrefl (this a (le_refl _))

def tendsto_atTop_atTop_of_monotone
  [OrderOps β] [IsPreOrder α] [IsPreOrder β] {f : α → β} (hf : Monotone f)
  (h : ∀ b, ∃ a, b ≤ f a) : TendsTo f atTop atTop := by
  erw [tendsto_iInf]
  intro b
  rw [tendsto_principal]
  simp
  have ⟨a, b_le_fb⟩ := h b
  apply FilterBase.closed_upward
  apply mem_atTop
  assumption
  intro x hx
  simp at *
  apply le_trans
  assumption
  apply hf
  assumption

def tendsto_atBot_atBot_of_monotone
  [OrderOps β] [IsPreOrder α] [IsPreOrder β] {f : α → β} (hf : Monotone f)
  (h : ∀ b, ∃ a, f a ≤ b) : TendsTo f atBot atBot :=
  tendsto_atTop_atTop_of_monotone (α := αᵒᵖ) (β := βᵒᵖ) hf.dual h

end

end Filter
