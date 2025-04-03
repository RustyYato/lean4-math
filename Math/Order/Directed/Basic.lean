import Math.Data.Set.Basic
import Math.Order.Defs

variable {α : Type u} {β : Type v} {ι : Sort w} (r r' s : α → α → Prop)

def Directed (f: ι -> α) := ∀a b, ∃c, r (f a) (f c) ∧ r (f b) (f c)

namespace Set

def DirectedOn (s: Set α) := ∀a ∈ s, ∀b ∈ s, ∃c ∈ s, r a c ∧ r b c

def DirectedOn.iff_directed : DirectedOn r S ↔ Directed r fun x: S => x.val := by
  apply Iff.intro
  intro h a b
  have ⟨c, hc, _, _⟩ := h a.val a.property b.val b.property
  exists ⟨c, hc⟩
  intro h a ha b hb
  have ⟨c, _, _⟩ := h ⟨a, ha⟩ ⟨b, hb⟩
  refine ⟨c, c.property, ?_, ?_⟩ <;> assumption

end Set

class IsDirected (α: Type*) (r: α -> α -> Prop) where
  isDirected : Directed r id

instance [LE α] [Top α] [IsLawfulTop α] : IsDirected α (· ≤ ·) where
  isDirected := by
    intro a b
    exists ⊤
    apply And.intro
    apply le_top
    apply le_top

instance [LE α] [Bot α] [IsLawfulBot α] : IsDirected α (· ≥ ·) where
  isDirected := by
    intro a b
    exists ⊥
    apply And.intro
    apply bot_le
    apply bot_le

instance [LE α] [LT α] [Max α] [IsSemiLatticeMax α] : IsDirected α (· ≤ ·) where
  isDirected := by
    intro a b
    exists max a b
    apply And.intro
    apply le_max_left
    apply le_max_right

instance [LE α] [LT α] [Min α] [IsSemiLatticeMin α] : IsDirected α (· ≥ ·) where
  isDirected := by
    intro a b
    exists min a b
    apply And.intro
    apply min_le_left
    apply min_le_right

def isDirected (r: α -> α -> Prop) [h: IsDirected α r] := h.isDirected
