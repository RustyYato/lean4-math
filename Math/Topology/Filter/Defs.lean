import Math.Topology.Basic
import Math.Order.Filter.Basic

variable [Topology α]

open FilterBase Topology

namespace Topology

/-- a set is a neighborhood if it contains an open set around x
    and the set of all neighborhoods is a filter --/
def nhds (a: α) : Filter α :=
  ⨅x: Set.mk (fun s: Set α => a ∈ s ∧ IsOpen s), 𝓟 x.val

@[inherit_doc]
scoped notation "𝓝" => nhds

/-- The "neighborhood within" filter. Elements of `𝓝[s] x` are sets containing the
    intersection of `s` and a neighborhood of `x`. -/
def nhdsWithin (x : α) (s : Set α) : Filter α := 𝓝 x ⊓ 𝓟 s

@[inherit_doc]
scoped notation "𝓝[" s "] " x:100 => nhdsWithin x s

def mem_nhds {a: α} : ∀{s}, s ∈ 𝓝 a ↔ ∃ t ⊆ s, IsOpen t ∧ a ∈ t := by
  intro S
  apply Iff.intro
  · intro h
    induction h with
    | basic h =>
      rename_i s
      simp at h
      rcases h with rfl | h
      refine ⟨⊤, ?_, ?_, ?_⟩
      rfl
      apply IsOpen.univ
      trivial
      replace ⟨_, ⟨_, ⟨⟨t, ht, topen⟩, rfl⟩, rfl⟩, h⟩ := Set.mem_sUnion.mp h
      refine ⟨t, ?_, ?_, ?_⟩
      assumption
      assumption
      assumption
    | up _ h ih =>
      obtain ⟨t', _, _, _⟩ := ih
      refine ⟨t', ?_, ?_, ?_⟩
      apply Set.sub_trans
      repeat assumption
    | min _ _ ih₀ ih₁ =>
      obtain ⟨t₀, _, _, _⟩ := ih₀
      obtain ⟨t₁, _, _, _⟩ := ih₁
      refine ⟨t₀ ∩ t₁, ?_, ?_, ?_⟩
      apply (Set.sub_inter _ _ _).mp
      apply And.intro
      apply flip Set.sub_trans
      assumption
      apply Set.inter_sub_left
      apply flip Set.sub_trans
      assumption
      apply Set.inter_sub_right
      apply IsOpen.inter
      assumption
      assumption
      apply And.intro
      assumption
      assumption
  · intro ⟨t, ht, topen, ha⟩
    apply FilterBase.GenerateSets.basic
    simp; right
    apply Set.mem_sUnion.mpr
    refine ⟨_, ⟨_, ⟨⟨t, ?_, ?_⟩, rfl⟩, rfl⟩, ?_⟩
    assumption
    assumption
    assumption

-- two points are inseparable iff their neighborhoods are equal
def Specializes (a b: α) := 𝓝 a ≤ 𝓝 b

-- two points are inseparable iff their neighborhoods are equal
def Inseparable (a b: α) := 𝓝 a = 𝓝 b

instance : Relation.IsRefl (Specializes (α := α)) where
  refl _ := le_refl _
instance : Relation.IsRefl (Inseparable (α := α)) where
  refl _ := rfl

instance {x: α} : NeBot (𝓝 x) where
  ne := by
    intro h
    have := mem_nhds (a := x) (s := ∅)
    rw [h] at this
    have ⟨_, h, _, _⟩  := this.mp (by trivial)
    cases Set.sub_empty _ h
    contradiction

-- the limit of a filter, if it exists
noncomputable def lim [Nonempty α] (f: Filter α) : α :=
  Classical.epsilon fun x => f ≤ 𝓝 x

def lim_spec [Nonempty α] (f: Filter α) (h: ∃x, f ≤ 𝓝 x) : f ≤ 𝓝 (lim f) := Classical.epsilon_spec h

def IsClusterPoint (x: α) (F: Filter α) : Prop := NeBot (𝓝 x ⊓ F)

def IsCompactOn (S: Set α) : Prop :=
  ∀ ⦃F⦄ [NeBot F], F ≤ 𝓟 S -> ∃x ∈ S, IsClusterPoint x F

class IsCompactSpace (α: Type*) [Topology α] : Prop where
  univ_compact: IsCompactOn (⊤: Set α)

end Topology
